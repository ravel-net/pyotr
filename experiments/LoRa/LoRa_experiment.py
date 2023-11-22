import json



DEFAULTVALUES = {'UV': 0, 'Temperature': 31, 'Humidity': 66, 'Pressure': 1002, 'avgRain': 0, 'rainQty': 0, 'MQ4': 15, 'MQ7': 1, "pm10":37,"pm25":61,"pm100":72,"pm10_env":30,"pm25_env":48,"pm100_env":62, "um03":8322,"um05":2624,"um10":594,"um25":33,"um50":9,"um100":6, 'avgFlow': 0, 'Quantity': 0}

map_c_var = {}
i = -1
for colm in DEFAULTVALUES:
    map_c_var[colm] = i
    i -= 1

# devices has the format devices[ip] = [{time:time, data: data}]
def loadData(filename):
    with open(filename, 'r') as data_file:
        json_data = data_file.read()

    data = json.loads(json_data)
    devices = {}

    for dat in data:
        name = dat['ip']
        devicedata = dat['data']
        time = dat['addedDate']['$date']
        if name not in devices:
            devices[name] = []
        devices[name].append({"time":time, "data": devicedata})

    return devices

# dates = []

# for device in devices:
#     # print(len(devices[device]) ,device[7:], devices[device][0]["data"])
#     for data in devices[device]:
#         time = data["time"]
#         date = time.split('T')[0]
#         if date not in dates:
#             dates.append(date)

# for date in dates:
#     print(date)

# Send sensor data every x minutes
# Control over time
# Store data time wise (per minute)

# given a date string, returns the date and time (as minutes from midnight)
def getDateTime(dateStr):
    date = dateStr.split('T')[0]
    hourStr = dateStr.split('T')[1].split(':')[0]
    minutesStr = dateStr.split('T')[1].split(':')[1]
    minutes = int(hourStr)*60+int(minutesStr)
    return date, minutes

# returns min and max time for each day, with date as the key. Done using finding min and max time for each day
def loadTimeSorted(filename):
    with open(filename, 'r') as data_file:
        json_data = data_file.read()

    data = json.loads(json_data)
    times = {}

    for dat in data:
        dateStr = dat['addedDate']['$date']
        date, minutes = getDateTime(dateStr)
        if date not in times:
            times[date] = [1440,0] # min, max
        if minutes < times[date][0]:
            times[date][0] = minutes
        if minutes > times[date][1]:
            times[date][1] = minutes
    return times

# initializes first using times e.g. timeData[date][minutes] = []. Then fills it with devices and data
def loadDataPerTime(times, devices):
    timeData = {}
    # initialize
    for date in times:
        timeData[date] = {}
        min = times[date][0]
        max = times[date][1]
        i = min
        while i <= max:
            timeData[date][i] = []
            i += 1
    
    # fill
    for device in devices:
        for timeAndData in devices[device]:
            time  = timeAndData['time']
            data  = timeAndData['data']
            particles = {}
            if 'particles' in data:
                for um in data['particles']:
                    particles[um] = data['particles'][um]
                del data['particles']
                for um in particles:
                    data[um] = particles[um]

            date, minutes = getDateTime(time)
            # timeData[date][minutes].append({'name':device, 'data':data})
            timeData[date][minutes].append(data)
    return timeData

def reverseDict(dict):
    newDict = {}
    for key in dict:
        for colm in dict[key]:
            newDict[colm] = key
    return newDict

# given current minute and the value in pastData, return the condition of the value
def getCondition(colm, pastData, currDate, currMinute):
    c_var = colm
    pastVal = pastData[currDate][currMinute][colm] # pastVal has format {"value": .., "latestMinute": -1/...} where -1 represents default value
    value = pastVal["value"]
    latestMinute = pastVal["latestMinute"]
    minValue = int(float(value))-5
    if minValue < 0:
        minValue = 0
    maxValue = int(float(value))+5
    if float(value) == 0 or float(value) == 1:
        condition = "And({c_var} >= 0, {c_var} <= 1)".format(c_var=c_var)
    else:
        condition = "And({c_var} >= {minValue}, {c_var} <= {maxValue})".format(c_var=c_var, minValue=minValue, maxValue=maxValue)
    return c_var, condition

 # function that takes a tuple and returns the answers by categories. Takes the past data into account. cleanedData is a dictionary with category as key and array of tuples as value e.g. cleanedTuple = {1: [(c1,c2,c3,condition1),(b1,b2,b3,condition2)]}
def cleanTuple(tuple, categories, reversedCategories, pastData, currDate, currMinute, cleanedTuple):
    # find categories in tuple
    categoriesInTuple = []
    for colm in tuple:
        if colm == "Altitude":
            continue
        category = reversedCategories[colm]
        if category not in categoriesInTuple:
            categoriesInTuple.append(category)

    for category in categoriesInTuple:
        colms = categories[category]
        newTuple = []
        conditions = []
        for colm in colms:
            if colm in tuple:
                # newTuple.append(tuple[colm])
                newTuple.append(int(float((tuple[colm]))))
            else:
                c_var, condition = getCondition(colm, pastData, currDate, currMinute) # takes the past value of the current and the current minute as input and returns the uncertain tuple 
                conditions.append(condition)
                newTuple.append(map_c_var[c_var]) # maps c-variables to negative integers
        newTuple.append(conditions)
        if category not in cleanedTuple:
            cleanedTuple[category] = []
        cleanedTuple[category].append(newTuple)
    return cleanedTuple

# for all categories missing in cleanedTuple, fills them up with past data
def addMissingCategories(categories, reversedCategories, pastData, currDate, currMinute, cleanedTuple):
    for category in categories:
        if category in cleanedTuple:
            continue
        colms = categories[category]
        newTuple = []
        conditions = []
        for colm in colms:
            c_var, condition = getCondition(colm, pastData, currDate, currMinute) # takes the past value of the current and the current minute as input and returns the uncertain tuple 
            conditions.append(condition)
            newTuple.append(map_c_var[c_var]) # maps c-variables to negative integers
        newTuple.append(conditions)
        if category not in cleanedTuple:
            cleanedTuple[category] = []
        cleanedTuple[category].append(newTuple)

# for each minute returns the entire state of the database including conditions
def cleanData(timeData, categories, pastData):
    cleanedData = {}
    reversedCategories = reverseDict(categories)
    for date in timeData:
        print(date)
        cleanedData[date] = {}
        for minute in timeData[date]:
            cleanedData[date][minute] = {}
            cleanedTuple = {}
            for tuple in timeData[date][minute]:
                cleanTuple(tuple, categories, reversedCategories, pastData, date, minute, cleanedTuple) # function that takes a tuple and returns the answers by categories. Takes the past data into account. cleanedData is a dictionary with category as key and array of tuples as value e.g. cleanedTuple = {0: [], 1: [(c1,c2,c3,condition1),(b1,b2,b3,condition2)]}
            addMissingCategories(categories, reversedCategories, pastData, date, minute, cleanedTuple)
            cleanedData[date][minute] = cleanedTuple 
    print(cleanedData['2021-03-26'][600])

# returns data for all devices timeDataPastInfo[date][minute]['UV'] =  {"value": .., "latestMinute": -1/...}
def loadPastInfo(timeData):
    pastData = {}
    for date in timeData:
        pastData[date] = {}
        lastValue = {}
        for colm in DEFAULTVALUES:
            lastValue[colm] = {"value": DEFAULTVALUES[colm], "latestMinute":-1}
        for minute in timeData[date]:
            pastData[date][minute] = {}
            for tuple in timeData[date][minute]:
                for colm in tuple:
                    lastValue[colm] = tuple[colm]
                    lastValue[colm] = {"value": tuple[colm], "latestMinute":minute}
            for colm in lastValue:
                pastData[date][minute][colm] = lastValue[colm]
    return pastData



if __name__ == "__main__":
    devices = loadData('LoRa.json')
    times = loadTimeSorted('LoRa.json') # returns min and max time for each day, with date as the key. Done using finding min and max time for each day
    timeData = loadDataPerTime(times, devices) # initializes first using times e.g. timeData[date][minutes] = []. Then fills it with devices and data. e.g. timeData[date][minutes] = [{'colm1':val, 'colm2':val2},{},...]



    categories = {0:['UV'], 1:['Temperature', 'Humidity', 'Pressure'], 2:['avgRain','rainQty'], 3:['MQ4','MQ7'], 4:['pm10','pm25','pm100','pm10_env','pm25_env','pm100_env'], 5:['um03','um05','um10','um25','um50','um100'], 6:['avgFlow','Quantity']} # we have 7 categories

    pastData = loadPastInfo(timeData) # returns data for all devices timeDataPastInfo[date][minute]['UV'] =  {"value": .., "latestMinute": -1/...}

    cleanedData = cleanData(timeData, categories, pastData) # exact same format as timeData but the groups are divided based on data that we need for analysis


# Queries: Temperature is over 20 and MQ4 or MQ7 over 5
    # -> If for a minute, data from a device is unavailable, we assume that it's old data but add uncertainty. 
    # -> If no data available, we take average of the data but we don't need to talk about it in the paper
import json
import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
import os
print(root)
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
import psycopg2 
import databaseconfig as cfg
import time
from tabulate import tabulate
from copy import deepcopy
import logging


DEFAULTVALUES = {'UV': 0, 'Temperature': 31, 'Humidity': 66, 'Pressure': 1002, 'avgRain': 0, 'rainQty': 0, 'MQ4': 15, 'MQ7': 1, "pm10":37,"pm25":61,"pm100":72,"pm10_env":30,"pm25_env":48,"pm100_env":62, "um03":8322,"um05":2624,"um10":594,"um25":33,"um50":9,"um100":6, 'avgFlow': 0, 'Quantity': 0}

map_c_var = {}
i = -1
for colm in DEFAULTVALUES:
    map_c_var[colm] = i
    i -= 1


conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

# move this to table class
def printTable(tableName, db, nodeIntMappingReverse, condition = None):
    cursor = conn.cursor()
    # cursor.execute("SELECT * from {} where source = 1 and dest = 7".format(tableName))
    if condition:
        cursor.execute("SELECT * from {} where {}".format(tableName, condition))
    else:
        cursor.execute("SELECT * from {}".format(tableName))

    table = cursor.fetchall()
    newTable = []
    mapping = deepcopy(nodeIntMappingReverse)
    mapping.update(db.cVarMapping)
    print(mapping)
    for row in table:
        newRow = []
        for colm in row:
            if type(colm) == list:
                colmArray = []
                for item in colm:
                    colmArray.append(replaceVal(item, mapping))
                newRow.append(colmArray)
            else:
                newRow.append(replaceVal(colm, mapping))
        newTable.append(newRow)
    cursor.execute("SELECT column_name FROM information_schema.columns WHERE table_schema = 'public' AND table_name = '{}'".format(tableName.lower()))
    headers = cursor.fetchall()
    headerInArray = []
    for colm in headers:
        headerInArray.append(colm[0])
    print("\nPrinting Table: {}".format(tableName))
    print(tabulate(newTable, headers=headerInArray))

def replaceVal(val, mapping):
    if val in mapping:
        return mapping[val]
    elif str(val) in mapping:
        return mapping[str(val)]
    # elif type(val) == str:
    #     conditions = ConditionTree(val)
    #     return conditions.toString(mode = "Replace String", replacementDict = mapping)
    else:
        return val
    

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
        condition = "And({c_var} > -1, {c_var} < 2)".format(c_var=c_var)
    else:
        condition = "And({c_var} > {minValue}, {c_var} < {maxValue})".format(c_var=c_var, minValue=minValue, maxValue=maxValue)
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
    return cleanedData

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

def getInsertSQL(minute, category, tuples):
    insertStrs = []
    for tuple in tuples:
        insertStr = "(" + str(minute) + ", "
        for val in tuple[:-1]:
            insertStr += str(val) + ", "
        condition = ""
        if len(tuple[-1]) > 1:
            condition = "And(" + ",".join(tuple[-1]) + ")"
        elif len(tuple[-1]) == 1:
            condition = tuple[-1][0]
        if len(condition) > 0:
            insertStr += "'{\"" + condition + "\"}'"
        else:
            insertStr += "'{}'"
        insertStr += ")"
        insertStrs.append(insertStr)
    sql = "insert into T{} values ".format(str(category)) + ",".join(insertStrs) + " ON CONFLICT DO NOTHING;"
    return sql


# Runs the program for a single date
def runDatalogProgramPerDate(program, database, dataPerDate, frequency=5):
    # store first x items
    cursor = conn.cursor()
    sql = ""
    i = 0
    numRuns = 0
    for minute in dataPerDate:
        # insert data for a single minute
        for category in dataPerDate[minute]:
            sql += getInsertSQL(minute, category, dataPerDate[minute][category])
            # sql += getInsertSQL(minute, category, dataPerDate[minute][category])
        i += 1
        # every 'frequency' minute, run query and then delete database
        if i > 0 and (i % frequency == 0 or i == len(dataPerDate)):
            cursor.execute(sql)
            sql = ""
            program.execute(conn)
            conn.commit()
            # printTable("T0", database, {})
            # printTable("T1", database, {})
            # printTable("T2", database, {})
            # printTable("T3", database, {})
            # printTable("T4", database, {})
            # printTable("T5", database, {})
            # printTable("T6", database, {})
            # printTable("Ans", database, {})
            database.deleteAllTables(conn)
            numRuns += 1
    return numRuns

# runs a datalog program on the given data after storing data
def runDatalogProgram(program, database, data, frequency):
    numRuns = 0
    for date in data:
        print(date, frequency)
        numRuns += runDatalogProgramPerDate(program, database, data[date], frequency)
    return numRuns

# returns a datalog program with the data for LoRa
def getDatalogProgram(programStr, AnsTable):
    cVarMapping = {}
    for key in map_c_var:
        value = map_c_var[key]
        cVarMapping[str(value)] = key

    T0 = DT_Table(name="T0", columns={"Time":"integer", "UV":"integer_faure", "condition":"text[]"}, cvars={"UV":"UV"})
    T1 = DT_Table(name="T1", columns={"Time":"integer", "Temperature":"integer_faure", "Humidity":"integer_faure", "Pressure":"integer_faure", "condition":"text[]"}, cvars={"Temperature":"Temperature","Humidity":"Humidity","Pressure":"Pressure"})
    T2 = DT_Table(name="T2", columns={"Time":"integer", "avgRain":"integer_faure", "rainQty":"integer_faure", "condition":"text[]"}, cvars={"rainQty":"rainQty","avgRain":"avgRain"})
    T3 = DT_Table(name="T3", columns={"Time":"integer", "MQ4":"integer_faure", "MQ7":"integer_faure", "condition":"text[]"}, cvars={"MQ4":"MQ4","MQ7":"MQ7"})
    T4 = DT_Table(name="T4", columns={"Time":"integer", "pm10":"integer_faure", "pm25":"integer_faure", "pm100":"integer_faure", "pm10_env":"integer_faure", "pm25_env":"integer_faure", "pm100_env":"integer_faure", "condition":"text[]"}, cvars={"pm10":"pm10","pm25":"pm25","pm100":"pm100","pm10_env":"pm10_env","pm25_env":"pm25_env","pm100_env":"pm100_env"})
    T5 = DT_Table(name="T5", columns={"Time":"integer", "um03":"integer_faure", "um05":"integer_faure", "um10":"integer_faure", "um25":"integer_faure", "um50":"integer_faure", "um100":"integer_faure", "condition":"text[]"}, cvars={"um03":"um03","um05":"um05","um10":"um10","um25":"um25","um50":"um50","um100":"um100"})
    T6 = DT_Table(name="T6", columns={"Time":"integer", "avgFlow":"integer_faure", "Quantity":"integer_faure", "condition":"text[]"}, cvars={"avgFlow":"avgFlow","Quantity":"Quantity"})

    database = DT_Database(tables=[T0,T1,T2,T3,T4,T5,T6,AnsTable], cVarMapping = cVarMapping)
  
    program = DT_Program(programStr, database=database, optimizations={"simplification_on":True, "recursive_rules":False}, reasoning_engine="z3")
    database.initiateDB(conn)
    conn.commit()
    return program, database

def analyze(numRuns, frequency, filename="program.log", outputfile="LoRa.dat"):
    sums = {}
    with open(filename) as f:
        lines = f.readlines()
        for line in lines:
            if "Time" in line:
                data = line.split()
                function = data[1]
                time = float(data[-1])
                if function not in sums:
                    sums[function] = []
                sums[function].append(time)

    with open(outputfile,"a") as f:
        executeTime = sum(sums["DT_Program_execute"])
        dbTime = sum(sums["db_z3"])
        reasoningTime = sum(sums["reasoning_z3"])
        executeTimeRemaining = executeTime-dbTime-reasoningTime
        f.write("{}\t{}\t{}\t{}\n".format(str(frequency), str(dbTime/numRuns), str(reasoningTime/numRuns), str(executeTimeRemaining/numRuns)))

    with open("length","a") as f:
        executeTime = len(sums["DT_Program_execute"])
        dbTime = len(sums["db_z3"])
        reasoningTime = len(sums["reasoning_z3"])
        executeTimeRemaining = executeTime-dbTime-reasoningTime
        f.write("{}\t{}\t{}\t{}\n".format(str(frequency), str(dbTime), str(reasoningTime), str(executeTimeRemaining)))
                
if __name__ == "__main__":
    devices = loadData('LoRa.json')

    times = loadTimeSorted('LoRa.json') # returns min and max time for each day, with date as the key. Done using finding min and max time for each day
    timeData = loadDataPerTime(times, devices) # initializes first using times e.g. timeData[date][minutes] = []. Then fills it with devices and data. e.g. timeData[date][minutes] = [{'colm1':val, 'colm2':val2},{},...]

    categories = {0:['UV'], 1:['Temperature', 'Humidity', 'Pressure'], 2:['avgRain','rainQty'], 3:['MQ4','MQ7'], 4:['pm10','pm25','pm100','pm10_env','pm25_env','pm100_env'], 5:['um03','um05','um10','um25','um50','um100'], 6:['avgFlow','Quantity']} # we have 7 categories

    pastData = loadPastInfo(timeData) # returns data for all devices timeDataPastInfo[date][minute]['UV'] =  {"value": .., "latestMinute": -1/...}

    cleanedData = cleanData(timeData, categories, pastData) # exact same format as timeData but the groups are divided based on data that we need for analysis


    ####################################################### Join Experiments ###############################################
    Queries = []
    programStr = "Ans(t, temp) :- T1(t, temp, humid, press)[And(temp < 35)]"
    AnsTable = DT_Table(name="Ans", columns={"Time":"integer", "Temperature":"integer_faure", "condition":"text[]"}, cvars={"Temperature":"Temperature"})
    Queries.append((programStr, AnsTable, 1))

    programStr = "Ans(t, temp, m4) :- T1(t, temp, humid, press)[And(temp < 35)], T3(t,m4,m7)[m4 == 4]"
    AnsTable = DT_Table(name="Ans", columns={"Time":"integer", "Temperature":"integer_faure", "MQ4":"integer_faure", "condition":"text[]"}, cvars={"Temperature":"Temperature","MQ4":"MQ4"})
    Queries.append((programStr, AnsTable, 2))

    programStr = "Ans(t, temp, m4, p10) :- T1(t, temp, humid, press)[And(temp < 35)], T3(t,m4,m7)[m4 == 4], T4(t, p10, p25, p100, p10env, p25env, p100env)[p10 > 33]"
    AnsTable = DT_Table(name="Ans", columns={"Time":"integer", "Temperature":"integer_faure", "MQ4":"integer_faure",  "pm10":"integer_faure", "condition":"text[]"}, cvars={"Temperature":"Temperature","MQ4":"MQ4","pm10":"pm10"})
    Queries.append((programStr, AnsTable, 3))

    programStr = "Ans(t, temp, m4, p10, u05) :- T1(t, temp, humid, press)[And(temp < 35)], T3(t,m4,m7)[m4 == 4], T4(t, p10, p25, p100, p10env, p25env, p100env)[p10 > 33], T5(t, u03, u05, u10, u25, u50, u100)[u05 > 3000]"
    AnsTable = DT_Table(name="Ans", columns={"Time":"integer", "Temperature":"integer_faure", "MQ4":"integer_faure", "pm10":"integer_faure", "um05":"integer_faure", "condition":"text[]"}, cvars={"Temperature":"Temperature","MQ4":"MQ4","pm10":"pm10", "um05":"um05"})
    Queries.append((programStr, AnsTable, 4))

    programStr = "Ans(t, temp, m4, p10, avgF, u05) :- T1(t, temp, humid, press)[And(temp < 35)], T3(t,m4,m7)[m4 == 4], T4(t, p10, p25, p100, p10env, p25env, p100env)[p10 > 33], T5(t, u03, u05, u10, u25, u50, u100)[u05 > 3000], T2(t, avgF, quant)[avgF > 5]"
    AnsTable = DT_Table(name="Ans", columns={"Time":"integer", "Temperature":"integer_faure", "MQ4":"integer_faure", "pm10":"integer_faure", "avgFlow":"integer_faure", "um05":"integer_faure", "condition":"text[]"}, cvars={"Temperature":"Temperature","MQ4":"MQ4","pm10":"pm10", "avgFlow":"avgFlow", "um05":"um05"})
    Queries.append((programStr, AnsTable, 5))


    frequency = 10

    filename = "program.log"

    outputFile = "LoRa_tables.dat"
    with open(outputFile,"w") as f:
        f.write("Tables\tDB\tReasoning\tSystem\n")

    for queryTuple in Queries:
        programStr = queryTuple[0]
        AnsTable = queryTuple[1]
        numTables = queryTuple[2]
        program, database = getDatalogProgram(programStr, AnsTable)
        numRuns = runDatalogProgram(program, database, cleanedData, frequency=frequency)
        logging.shutdown()
        analyze(numRuns, numTables, filename, outputFile)
        os.remove(filename)


    ####################################################### Frequency Experiments ###############################################
    # programStr = "Ans(t, temp, m4) :- T1(t, temp, humid, press)[And(temp > 30)], T3(t,m4,m7)[m4 == 4]"
    # # programStr = "Ans(t, temp, p10) :- T1(t, temp, humid, press)[And(temp > 30)], T4(t, p10, p25, p100, p10env, p25env, p100env)[p10 == 33]"

    # AnsTable = DT_Table(name="Ans", columns={"Time":"integer", "Temperature":"integer_faure", "MQ4":"integer_faure", "condition":"text[]"}, cvars={"Temperature":"Temperature","MQ4":"MQ4"})

    # with open("LoRa.dat","w") as f:
    #         f.write("Frequency\tDB\tReasoning\tSystem\n")

    # program, database = getDatalogProgram(programStr, AnsTable)
    # frequencies = [10,15,20,25]
    # filename = "program.log"
    # for frequency in frequencies:
    #     numRuns = runDatalogProgram(program, database, cleanedData, frequency=frequency)
    #     logging.shutdown()
    #     analyze(numRuns, frequency, filename)
    #     os.remove(filename)

# Queries: Temperature is over 20 and MQ4 or MQ7 over 5
    # -> If for a minute, data from a device is unavailable, we assume that it's old data but add uncertainty. 
    # -> If no data available, we take average of the data but we don't need to talk about it in the paper
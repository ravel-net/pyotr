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
import random
import statistics
import math

# devices has the format devices[ip] = [{time:time, data: data}]
def loadData(filename, type):
    with open(filename, 'r') as data_file:
        json_data = data_file.read()

    data = json.loads(json_data)
    devices = {}

    for dat in data:
        if type in dat['data']:
            name = "measuredDevice"
        else:
            name = dat['ip']
        devicedata = dat['data']
        time = dat['addedDate']['$date']
        date, minutes = getDateTime(time)
        if name not in devices:
            devices[name] = {}
        if date not in devices[name]:
            devices[name][date] = []
        devices[name][date].append(devicedata)

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

def getFuzzedDataBaseline(deviceData, type, fuzzPercentage):
    newData = {} # format: newData[date] = [temp1,temp2,]
    for date in deviceData:
        newData[date] = []
        i = 0
        for data in deviceData[date]:
            randNumber = random.randint(0, 99)
            if randNumber >= fuzzPercentage or i == 0: # if not random
                newData[date].append(float(data[type]))
            else:
                newData[date].append(float(newData[date][i-1])) # else use past data
            i += 1
    return newData


# given a date string, returns the date and time (as minutes from midnight)
def getDateTime(dateStr):
    date = dateStr.split('T')[0]
    hourStr = dateStr.split('T')[1].split(':')[0]
    minutesStr = dateStr.split('T')[1].split(':')[1]
    minutes = int(hourStr)*60+int(minutesStr)
    return date, minutes

def getStdDev(groundTruth, date):
    return statistics.stdev(groundTruth[date])

# calculates euclidian distance between two data points while keeping standard deviation into account
def getError(groundTruth, baselineData, std, exceptDate):
    sum = 0
    for date in baselineData:
        if date == exceptDate:
            continue
        i = 0
        for data in baselineData[date]:
            groundData = groundTruth[date][i]
            
            if groundData > (data+std):
                newDatapoint = data+std
                distance = math.pow((groundData-newDatapoint),2)
            elif groundData < (data-std):
                newDatapoint = data-std
                distance = math.pow((groundData-newDatapoint),2)
            else: # match within std!
                distance = 0
            sum += distance
            i += 1
    return math.sqrt(sum)

if __name__ == "__main__":
    percentages = [10, 20, 30, 40, 50]
    types = ['pm10','pm25','pm100','pm10_env','pm25_env','pm100_env']
    errorBaseline = 0
    errorPyotr = 0

    for fuzzPercentage in percentages:
        for type in types:
            devices = loadData('LoRa.json', type)
            device = "measuredDevice"
            date = "2021-03-31"

            groundTruth = getFuzzedDataBaseline(devices[device], type, 0)
            baselineData = getFuzzedDataBaseline(devices[device], type, fuzzPercentage) # fills the baseline with fuzzed data assuming past data
            std = getStdDev(groundTruth, date)
            errorBaseline += getError(groundTruth, baselineData, std=0, exceptDate=date)
            errorPyotr += getError(groundTruth, baselineData, std=std, exceptDate=date)
        print(fuzzPercentage, errorPyotr, errorBaseline)
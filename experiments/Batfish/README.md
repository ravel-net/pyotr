# Result

## Batfish

|topo1|topo2|runtime (seconds)|is_equal|
|---|---|---|---|
|t1|t2|2.506450653076172|False|
|t1|t3|3.017583131790161|False|
|t1|t4|2.2334206104278564|True|
|t2|t1|2.2448434829711914|False|
|t2|t3|2.4925668239593506|True|
|t2|t4|2.223583936691284|False|
|t3|t1|2.2630832195281982|False|
|t3|t2|2.982739210128784|True|
|t3|t4|2.2471768856048584|False|
|t4|t1|2.2188050746917725|True|
|t4|t2|2.236191987991333|False|
|t4|t3|2.710930109024048|False|

## Pyotr(symbolic and no acl added)


|program|input|runtime (seconds) |is_tautology|model|
|---|---|---|---|---|
|t1|t2|2.9772861003875732|False|[x = 0, w = 1, v = 1, u = 2, y = 1]|
|t1|t3|1.2281668186187744|False|[x = 0, w = 1, v = 1, y = 1]|
|t2|t1|2.5019428730010986|True||
|t2|t3|0.9858429431915283|True||
|t3|t1|0.7085597515106201|True||
|t3|t2|0.8010566234588623|True||

## Pyotr(symbolic, no ACL, constant instance)

convert u to 3, v to 4, w to 5

|query|instance|runtime (seconds) |is_equal|model|
|---|---|---|---|---|
|t1|t2|0.18376946449279785|False|[[x = 0, y = 0], [x = 0, y = 1]]|
|t1|t3|0.1835331916809082|False|[[x = 0, y = 0], [x = 0, y = 1]]|
|t2|t1|0.17490148544311523|True||
|t2|t3|0.12439990043640137|True||
|t3|t1|0.1782524585723877|True||
|t3|t2|0.11272382736206055|True||

## Pyotr(symbolic, ACL(text))

Encoding example(T3):
|n1|n2|acl||
|--|--|--|--|
|1|2|'acl1'|x=1|
|1|v|'acl1'|x=0|
|2|v|'acl2'|y=1|
|2|w|'acl2'|y=0|
|v|w|'acl0'||

**Results:**
|query|instance|runtime(seconds)|is_equal|counter-example|
|---|---|---|---|---|
|t1|t2|1.4284954071044922|False|[[x = 0, y = 0], [x = 0, y = 1], [x = 1, y = 0]]|
|t1|t3|0.9219017028808594|False|[[x = 0, y = 0], [x = 0, y = 1], [x = 1, y = 0]]|
|t1|t4|1.079089641571045|False|[[x = 0, y = 0], [x = 0, y = 1], [x = 1, y = 0]]|
|t2|t1|1.0633838176727295|False|[[x = 0, y = 0], [x = 0, y = 1], [x = 1, y = 1]]|
|t2|t3|0.6407387256622314|False|[[x = 0, y = 0], [x = 0, y = 1], [x = 1, y = 1]]|
|t2|t4|0.8235905170440674|False|[[x = 0, y = 0], [x = 0, y = 1], [x = 1, y = 1]]|
|t3|t1|0.38840198516845703|False|[[x = 0, y = 0], [x = 0, y = 1]]|
|t3|t2|0.43981337547302246|False|[[x = 0, y = 0], [x = 0, y = 1]]|
|t3|t4|0.37788963317871094|False|[[x = 0, y = 0], [x = 0, y = 1]]|
|t4|t1|0.34030866622924805|False|[[x = 0, y = 0], [x = 0, y = 1]]|
|t4|t2|0.4017467498779297|False|[[x = 0, y = 0], [x = 0, y = 1]]|
|t4|t3|0.2933778762817383|False|[[x = 0, y = 0], [x = 0, y = 1]]|

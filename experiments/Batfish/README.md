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
|query|instance|runtime (seconds) |is_equal|model|
|---|---|---|---|---|
|t1|t2|0.18801259994506836|False|[x = 0, y = 0]|
|t1|t3|0.18167948722839355|False|[x = 0, y = 0]|
|t2|t1|0.16520977020263672|True||
|t2|t3|0.12062859535217285|True||
|t3|t1|0.16416454315185547|True||
|t3|t2|0.11152076721191406|True||

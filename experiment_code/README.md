# Hotnet21 experiment code

## Realistic Topology 

[RouteView](http://www.routeviews.org/routeviews/) RIB file and UPDATE file

Source: route-views2.oregon-ix.net

Date: 2021-06-10 10:00

The format of RIB file:

- #0  -> BGP protocol
- #1  -> unix time in seconds
- #2  -> Withdraw or Announce  (B)
- #3  -> PeerIP
- #4  -> PeerAS
- #5  -> Prefix
- #6  -> AS_PATH
- #7  -> Origin
- #8  -> Next_Hop
- #9  -> Local_Pref
- #10 -> MED
- #11 -> Community
- #12 -> AtomicAGG
- #13 -> AGGREGATOR

## Python package dependencies
- psycopg2-binary
- tqdm
- z3-solver

## RouteView - RIB and UPDATE FILE

### Convert ***rib.bz2*** to ***rib.txt***

```
bgpdump -m -O rib.txt rib.bz2
```
Or
```
bgpreader -d singlefile -o rib-file=rib.bz2 -m > rib.txt
```

### Convert ***update.bz2*** to ***update.txt***

```
bgpreader -d singlefile -o upd-file=update.bz2 -m > update.txt
```

## Walkthrough

### Load topo into database by using *gen_ribDB.py*

```python
# create table rib0610
gen_raw_rib_table(filename='rib0610.txt', table_name='rib0610')

# generate subset of rib file with different size of prefixes
sizes = [1000, 10000, 100000, 922067]
for size in sizes:
    gen_subset_rib(size)
```

### Generate F table by using gen_f_table.py

```python
sizes = [1000, 10000, 100000, 922067]
for size in sizes:
    tablename = 'rib' + str(size)
    gen_f_table(tablename=tablename)

    # create index for fid, mark attribute in F table
    create_index_fid_mark(tablename='f_table_'+tablename)
```

### Generate R table by using gen_r_table.py

```python
tablenames = ['rib1000', 'rib10000', 'rib100000', 'rib922067']
num = 10 # recursive times

for table in tablenames:
    gen_r_table(num=num, tablename=table)

    # create index for source, dest, fid attributes in R table
    create_index_source_dest_fid(tablename= table + '_r')
```

### Run query by using queries_on_r_2.py

Using q6 as example.

```python
tablenames = ['rib1000', 'rib10000', 'rib100000', 'rib922067']
r_tables = ['rib1000_r', 'rib10000_r', 'rib100000_r', 'rib922067_r']
ftablenames = ['f_table_rib1000', 'f_table_rib10000', 'f_table_rib100000', 'f_table_rib922067']
times = [1, 1, 1, 1]

for count in range(0,4):
    for i in range(times[count]):
        # SQL part 
        q6(r_table=r_tables[count], f_table=ftablenames[count], output='t1_'+tablenames[count])
        # Z3 part - remove contradition
        rem_contrad(tablename='t1_'+tablenames[count])
```
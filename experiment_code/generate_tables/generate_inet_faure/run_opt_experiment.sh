cd ../../../dataypes/inet_faure/opt
rm *.bc *.o *.so
make
psql -U postgres -d test -a -f inet_faure.sql
cd ../../../
psql -U postgres -d test -a -f ./experiment_code/drop_extra.sql
cd ./experiment_code/generate_tables/generate_inet_faure
python3 gen_ribDB.py 100 1000
python3 gen_f_table.py 100 1000
python3 gen_r_table.py 100 1000
cd ../
python3 test_sql_generator.py "test1.sql" "inet_join_1000.txt" 20 "select f_table_rib1000.nid1, f_table_rib1000.nid2 from f_table_rib1000, rib1000 where (f_table_rib1000.fid & '255.255.0.0/16') = (rib1000.prefix & '255.255.0.0/16');"
psql -U postgres -d test -a -f test1.sql
python3 collect_stats.py "inet_join_1000.txt" > "inet_join_1000_20.txt"
cd ../../dataypes/inet_faure
rm *.bc *.o *.so
make
psql -U postgres -d test -a -f inet_faure.sql
cd ../../
psql -U postgres -d test -a -f ./experiment_code/drop_extra.sql
cd ./experiment_code/generate_tables
python3 generate_table.py inet_faure f_table_inet.txt rib1000_inet.txt
python3 test_sql_generator.py "test2.sql" "inet_faure_project_1000.txt" 20 "select prefix & '255.255.0.0/16' from rib1000;"
psql -U postgres -d test -a -f test2.sql
python3 collect_stats.py "inet_faure_project_1000.txt" > "inet_faure_project_1000_20.txt"
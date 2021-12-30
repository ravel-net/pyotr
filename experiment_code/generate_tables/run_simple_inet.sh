# psql -U postgres -d test -a -f ../drop_extra.sql
# python3 generate_table.py inet f_table_inet.txt rib1000_inet.txt
python3 test_sql_generator.py "test1.sql" "inet_postgres_select_1000.txt" 20 "select * from rib1000 where prefix & '255.255.0.0/16' = '5.8.0.0/24';"
psql -U postgres -d test -a -f test1.sql
python3 collect_stats.py "inet_postgres_select_1000.txt" > "inet_postgres_select_1000_20.txt"

psql -U postgres -d test -a -f ../drop_extra.sql
python3 generate_table.py inet f_table_inet.txt rib1000_inet.txt
python3 test_sql_generator.py "test1.sql" "inet_postgres_join_1000.txt" 1 "select f_table_rib1000.id from f_table_rib1000, rib1000 where f_table_rib1000.fid = rib1000.prefix;"
psql -U postgres -d test -a -f test1.sql
python3 collect_stats.py "inet_postgres_join_1000.txt" > "inet_postgres_join_1000_20.txt"

# sudo -u postgres -i
# psql -U postgres -d test -a -f /home/mudbri/Documents/GitHub/pyotr/experiment_code/drop_extra.sql
python3 gen_ribDB.py 100 1000
python3 gen_f_table.py 100 1000
python3 gen_r_table.py 100 1000
# cd ../
# python2 queries_on_r_2.py > text_rib1000_results.txt


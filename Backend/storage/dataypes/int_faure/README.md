# int4faure
`int4faure` is a special data type that behaves exactly like the 4 byte Integer datatype of postgresql except that it also supports c-variables. A c-variable is identified by text character and can take any integer value. For all comparison funcitions, whenever there is a c-variable involved, the answer is always true.

The below menitoned instructions _install_ the `int4faure` type in a given database.

# Synposis
```
make
sudo -u [postgres username] -i
psql -U [postgres username] -d [database name] -a -f [current folder location]/int_faure.sql
```
Make sure that the database name and postgres user correspond to the one given in the database configuration file: https://github.com/ravel-net/pyotr/blob/cleanup/databaseconfig.py

# Example
If the postgres username is _postgres_, database name is _testDB_, and the root folder is at _/home/mudbri/pyotr/_ then the installation looks like the following: 
```
make
sudo -u postgres -i
psql -U postgres -d testDB -a -f /home/mudbri/pyotr/Backend/storage/dataypes/int_faure/int_faure.sql
```

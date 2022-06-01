# -*- coding: UTF-8 -*-
import psycopg2

class DB:
    def __init__(self, 
                host="127.0.0.1", 
                db="mydb", 
                user="ethan", 
                pwd="ethan"):
        self.host = host
        self.db = db
        self.user = user
        self.pwd = pwd
        self._connect()
        self._cursor = self._conn.cursor()

    def try_except(self):
        def wrapper(*args, **kwargs):
            try:
                self(*args, **kwargs)
            except Exception as e:
                print("get error: %s" % e)
        return wrapper

    @try_except
    def _connect(self):
        self._conn = psycopg2.connect(
            database=self.db,
            user=self.user,
            password=self.pwd,
            host=self.host)

    @try_except
    def select(self, sqlCode):
        self._cursor.execute(sqlCode)

    def insert(self, sqlCode):
        self.common(sqlCode)
    
    def insertmany(self, sqlCode, vars_list):
        self._cursor.executemany(sqlCode, vars_list)
        self._conn.commit()

    def update(self, sqlCode):
        self.common(sqlCode)

    def delete(self, sqlCode):
        self.common(sqlCode)

    def close(self):
        self._cursor.close()
        self._conn.close()
  
    def insertAndGetField(self, sql_code, field):
        """
        insert data and return current field
        :param sql_code:
        :param field:
        :return:
        """
        try:
            self.cursor.execute(sql_code + " RETURNING " + field)
        except Exception as e:
            print(e)
            self._conn.rollback()
            self._cursor.execute(sql_code + " RETURNING " + field)
        self._conn.commit()

        return self._cursor.fetchone()

    def common(self, sqlCode):
        try:
            self._cursor.execute(sqlCode)
        except Exception as e:
            print(e)
            self._conn.rollback()
            self._cursor.execute(sqlCode)
        self._conn.commit()

    def __del__(self):
        # print("close connect")
        self.close()


if __name__ == '__main__':
    db = DB()
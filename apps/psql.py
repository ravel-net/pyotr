"""
PostgreSQL sub-shell

PostgreSQL sub-shell is a core application that is enabled by default.
"""

import psycopg2
import tabulate
import os
from ravel.app import AppConsole

class PSqlConsole(AppConsole):
    def default(self, line):
        "Execute a PostgreSQL statement"
        try:
            self.db.cursor.execute(line)

            # TODO: A very hacky way to load inet_faure dataype. Move this to sarasate.sql with a relative path
            if (line == "CREATE TYPE inet_faure"):
                script_dir = os.path.dirname(__file__) #<-- absolute dir the script is in
                rel_path = "../dataypes/inet_faure/inet_faure.sql"
                abs_file_path = os.path.join(script_dir, rel_path)
                self.db.cursor.execute(open(abs_file_path, "r").read())
        except psycopg2.ProgrammingError as e:
            print(e)
            return

        try:
            data = self.db.cursor.fetchall()
            if data is not None:
                names = [row[0] for row in self.db.cursor.description]
                print(tabulate.tabulate(data, headers=names))
        except psycopg2.ProgrammingError:
            # no results, eg from an insert/delete
            pass
        except TypeError as e:
            print(e)

shortcut = "p"
description = "execute a PostgreSQL statement"
console = PSqlConsole


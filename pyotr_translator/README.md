# Translator_pyotr

This translator is the baseline of old faure but supports multiple joins and batch process on z3 step. This translator file is a python script that help do the expeiment conveniently and cannot use in the Ravel terminal.

## Difference between Faure translator and Pyotr translator

- `data()`: the Faure translator uses user-defined functions(i.e. equal(), not_equal()) in where clause, the Pyotr translator uses int4_faure built-in operators in where clause.

- `normalization()`: the Faure translator uses string type in z3 object, the Pyotr translator uses int type in z3 object.

## Database configuration

See `README` in the `faure_translator` folder. 


## translator usage

See `README` in the `faure_translator` folder. 

## Z3 part

We use the Z3 SMT solver checking the conditions which are contradiction, which are tautology and which are satisfiable. 

Relational algebra on c-tables are implemented by three steps: create data content, update conditions and normalization. Normalization includes removing tuples whose condition is contradiction, simplifying conditions who has redundant conditions and who are tautology. Normalization uses z3 SMT solver. 

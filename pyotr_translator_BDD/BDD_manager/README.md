# Instruction 

## Compilation and linkage

- install python-dev which includes header `"Python.h"`
  
```bash
sudo apt-get install python-dev
```

- Compile and install CUDD with option `./configure --enable-shared`

- run following command to compile and link it with Python system. 

```bash
python setup.py build
python setup.py install
```

- If cannot find related CUDD headers, export path of CUDD headers to `CPATH`.
```bash
export CPATH=/path/to/cudd/:/path/to/cudd/cudd/:/path/to/cudd/util
```

- If cannot find cudd library, copy `libcudd.so`, `libcudd-3.0.0.so.0` and `libcudd-3.0.0.so.0.0.0` to `/usr/lib/x86_64-linux-gnu/`. In addition, add `extra_link_args=['-L/usr/lib/x86_64-linux-gnu/']` to `setup.py`.

```bash
cp path/to/cudd/cudd/.libs/libcudd.so /usr/lib/x86_64-linux-gnu/
cp path/to/cudd/cudd/.libs/libcudd-3.0.0.so.0 /usr/lib/x86_64-linux-gnu/
cp path/to/cudd/cudd/.libs/libcudd-3.0.0.so.0.0.0 /usr/lib/x86_64-linux-gnu/
```
**setup.py**
```python
from distutils.core import setup, Extension

PATH = 'path/to/cudd'

MODULE = Extension(
    'BDD_managerModule', 
    include_dirs = [PATH+'/cudd', PATH+'/util', PATH+'/'],
    libraries = ['cudd', 'm'],
    library_dirs = [PATH+'/cudd/.libs/'],
    extra_link_args=['-L/usr/lib/x86_64-linux-gnu/'], # add this line
    sources = ['BDD_manager.c']
)

setup(
    name = 'BDD_managerModule',
    version='1.0',
    ext_modules=[MODULE]
)
```

## BDD_manager.c

Please find C APIs related information [here](https://github.com/ravel-net/pyotr/tree/CUDD/CUDD).









from distutils.core import setup, Extension

PATH = '/home/mudbri/cudd'


# setup(
#     name = 'BDD_managerModule',
#     version='1.0',
#     ext_modules=[Extension('_BDD_managerModule', ['BDD_manager.c'],
#                             swig_opts=['-I '+PATH+'/cudd', '-I '+PATH+'/util', '-L '+PATH+'/cudd/.libs/', '-lcudd', '-lm'])],
#     py_modules=['BDD_managerModule']
# )

MODULE = Extension(
    'BDD_managerModule', 
    include_dirs = [PATH+'/cudd', PATH+'/util', PATH+'/'],
    libraries = ['cudd', 'm'],
    library_dirs = [PATH+'/cudd/.libs/'],
    extra_link_args=['-L/usr/lib/x86_64-linux-gnu/'],
    sources = ['BDD_manager.c']
)

setup(
    name = 'BDD_managerModule',
    version='1.0',
    ext_modules=[MODULE]
)

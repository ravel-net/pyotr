from functools import wraps
import time
import logging
logging.basicConfig(filename='program.log', level=logging.DEBUG)
logging.debug('[Datalog] Start Logging ...')

def timeit(func):
    @wraps(func)
    def timeit_wrapper(*args, **kwargs):
        # logging.debug(f'Running Function {func.__name__}{args} {kwargs}')
        start_time = time.perf_counter()
        result = func(*args, **kwargs)
        end_time = time.perf_counter()
        total_time = end_time - start_time
        callerObject = str(args).split()[0].split(".")[-1]
        logging.info(f'Time: {callerObject}_{func.__name__} took {total_time:.4f}')
        return result
    return timeit_wrapper
Usage: ./memory_profiler.sh [program_name] [number of seconds to test memory]

Example: ./memory_profiler.sh run.py 30
This will run run.py and record memory every second for 30 seconds.

The memory results will be stored in "top_output.txt" while the program results will be stored in "results.txt". The memory is recorded every second but that can be changed by modifying the sleep period in the script
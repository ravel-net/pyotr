

# Results

**Terms:**
- `total`: total running time for the chase, including applying sigma 1 and sigma 2 as well as checking whether the answer is trivial.
- `check_applicable1`: running time for checking if there is tuple matching the tgd(sigma 1) pattern.
- `check_applicable12`: running time for checking if there is tuple matching the tgd(sigma 2) pattern.
- `insert_time1`: running time for inserting tuple when there is tuple matching the tgd(sigma 1) pattern.
- `insert_time2`: running time for inserting tuple when there is tuple matching the tgd(sigma 2) pattern.
- `check_trivial`: running time for checking whether the final answer is trivial.

## Figure 1(a)

**unit: millisecond**
|total|check_applicable1|check_applicable2|insert_time1|insert_time2|check_trivial|
|---|---|---|---|---|---|
|4.2516|1.2456|0.9258|0.6508|0.5842|0.8452|

## Figure 1(b)
**unit: millisecond**
|total|check_applicable1|check_applicable2|insert_time1|insert_time2|check_trivial|
|---|---|---|---|---|---|
|3.4206|1.1861|0.8630|0.6394|0.0000|0.7321|
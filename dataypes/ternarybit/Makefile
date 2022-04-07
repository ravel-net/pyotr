MODULES = ternarybit
DATA_built = ternarybit.sql

PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)

%.sql: %.source
	rm -f $@; \
	C=`pwd`; \
	sed -e "s:_OBJWD_:$$C:g" < $< > $@

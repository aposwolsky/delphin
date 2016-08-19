all: ;
	@echo "*************************************************"
	@echo "Creating Executable:  bin/elphin"
	@echo "*************************************************"
	mkdir -p bin/.heap
	sml < nabla.sml ;
	@echo "#! /bin/sh" > bin/elphin
	@echo "exec sml @SMLload=`pwd`/bin/.heap/elphin @SMLdebug=/dev/null" >> bin/elphin
	@chmod +x bin/elphin


clean: ;
	rm -rf bin/.heap/elphin* bin/elphin */CM

all: ;
	@echo "*************************************************"
	@echo "Creating Executable:  bin/delphin"
	@echo "*************************************************"
	mkdir -p bin/.heap
	sml < delphin.sml ;
	@echo "#! /bin/sh" > bin/delphin
	@echo "exec sml @SMLload=`pwd`/bin/.heap/delphin @SMLdebug=/dev/null" >> bin/delphin
	@chmod +x bin/delphin
	@echo ""
	@echo ""
	@echo "The Delphin executable is located at: bin/delphin"
	@echo "Send Questions or Comments to: adam@poswolsky.com"
	@echo ""
	@echo ""


clean: ;
	rm -rf bin/.heap/delphin* bin/delphin `find . -name 'CM'`
	rm -rf bin/delphin `find . -name '.cm'` `find . -name '.CM'`

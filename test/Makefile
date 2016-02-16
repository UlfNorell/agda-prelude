
agda = agda

default :
	$(agda) -i. -i../src Main.agda --compile $(agda-flags)

test :
	make agda-flags=--ignore-interfaces
	@if [ "`./Main`" == "`cat expected.out`" ]; \
			then echo "OK"; \
			else echo "Expected :\n`cat expected.out`"; \
					 echo "Output   :\n`./Main`"; \
					 false; \
	 fi


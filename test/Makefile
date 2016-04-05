
agda = agda

default : compile-main

everything :
	@echo "module Everything where" > Everything.agda
	@find ../src -name '*.agda' | sed -e 's/\.\.\/src\///;s/\//./g;s/\.agda$$//;s/^/import /' >> Everything.agda

compile-main :
	$(agda) Main.agda -c $(agda-flags)

compile-prime :
	$(agda) PrimeTest.agda -c $(agda-flags)

test : main-test prime-test

main-test : everything
	$(MAKE) compile-main agda-flags=--ignore-interfaces
	@if [ "`./Main`" == "`cat expected.out`" ]; \
			then echo "OK"; \
			else echo "Expected :\n`cat expected.out`"; \
					 echo "Output   :\n`./Main`"; \
					 false; \
	 fi

prime-test : compile-prime
	@if [ "`./PrimeTest`" == "true" ]; \
			then echo "OK"; \
			else echo "Fail:\n`./PrimeTest`"; false; \
	 fi


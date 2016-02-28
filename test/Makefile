
agda = agda

default : compile-main

compile-main :
	$(agda) Main.agda -c $(agda-flags)

compile-prime :
	$(agda) PrimeTest.agda -c $(agda-flags)

test : main-test prime-test

main-test :
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


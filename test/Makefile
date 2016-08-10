
agda = agda

default : compile-main

prof-flags=-prof -auto-all -osuf=p_o -hisuf=p_hi

everything :
	@echo "module Everything where" > Everything.agda
	@find ../src -name '*.agda' | sed -e 's/\.\.\/src\///;s/\//./g;s/\.agda$$//;s/^/import /' >> Everything.agda

compile-main :
	$(agda) Main.agda -c $(agda-flags)

compile-prime :
	$(agda) PrimeTest.agda -c $(agda-flags)

prof :
	$(agda) PrimeTest.agda -c $(patsubst %,--ghc-flag="%",$(prof-flags) -o PrimeTest_p)

test : main-test prime-test files-test

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

compile-files :
	$(agda) Files.agda -c $(agda-flags)

files-test : compile-files
	@./Files; \
   if [ $$? -eq 0 ]; \
			then echo "OK"; \
			else echo "Fail:\n`./Files`"; false; \
	 fi


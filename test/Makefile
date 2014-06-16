
agda = agda

default :
	$(agda) -i. -i../src Main.agda --compile --ghc-flag=-o --ghc-flag=hello $(agda-flags)

test :
	make agda-flags=--ignore-interfaces
	@if [ "`./hello`" == "Hello World" ]; \
			then echo "OK"; \
			else echo "Expected : Hello World"; \
					 echo "Output   : `./hello`"; \
					 false; \
	 fi


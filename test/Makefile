
agda = agda

default :
	$(agda) -i. -i../src Main.agda --compile --ghc-flag=-o --ghc-flag=hello $(agda-flags)

expected="0Hello1 World2"

test :
	make agda-flags=--ignore-interfaces
	@if [ "`./hello`" == $(expected) ]; \
			then echo "OK"; \
			else echo "Expected :" $(expected); \
					 echo "Output   : `./hello`"; \
					 false; \
	 fi


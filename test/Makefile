
agda = agda

default :
	$(agda) -i. -i../src Main.agda --compile --ghc-flag=../agda-ffi/Agda/FFI.hs $(agda-flags)

test :
	make agda-flags=--ignore-interfaces
	@if [ "`./Main`" == "`cat expected.out`" ]; \
			then echo "OK"; \
			else echo "Expected :\n`cat expected.out`"; \
					 echo "Output   :\n`./Main`"; \
					 false; \
	 fi


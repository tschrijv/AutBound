autbound : Tool/*.hs Tool/*/*.hs
	ghc Tool/*.hs Tool/**/*.hs -dynamic -o autbound
clean :
	rm asttool Tool/*.o Tool/*.hi Tool/*/*.o Tool/*/*.hi


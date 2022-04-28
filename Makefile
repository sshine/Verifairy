stack-build:
	stack build --flag diagnose:megaparsec-compat --flag diagnose:parsec-compat

uninstall-diagnose:
	# for when you accidentally compiled without the megaparsec flag WTF TODO
	stack exec -- ghc-pkg unregister --force diagnose


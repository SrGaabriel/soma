# Install somac
echo "Installing souls..."
lake build souls

cp -f ./compiler-lean/.lake/build/bin/somac ~/.sup/bin/somac

# Install souls
echo "Installing souls..."
lake build souls

cp -f ./souls-lean/.lake/build/bin/souls ~/.sup/bin/souls
# Install souls
echo "Installing souls..."
lake build souls

cp -f ./souls-lean/.lake/build/bin/souls ~/.sup/bin/souls
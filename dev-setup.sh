# Install somac
echo "Installing somac..."
lake build somac

ln -sf ./compiler-lean/.lake/build/bin/somac ~/.sup/bin/somac

# Install souls
echo "Installing souls..."
lake build souls

ln -sf ./souls-lean/.lake/build/bin/souls ~/.sup/bin/souls
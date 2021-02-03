#!/bin/bash

# only if the replacement doesn't exist
if ! grep -r -w $2_corres .;
  then
  # search and replace
  find . -type f -exec sed -i "s/\b$1\b/$2_corres/g" {} +
  # commit the change
  git commit -am "rename $1 to $2_corres"
else
  echo "Replacement string already exists"
fi

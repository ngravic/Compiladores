#!/bin/bash

for FILE in tests/good/*.tig; 
do
  echo $FILE; 
  echo;
  ./tiger $FILE; 
  echo; 
done


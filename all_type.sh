#!/bin/bash

for FILE in tests/type/*.tig; 
do
  echo $FILE;
  echo ==========================================
  echo Contenido
  cat $FILE
  echo -----------------------------------------
  echo;
  ./tiger $FILE; 
  echo; 
done


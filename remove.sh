#!/bin/bash

###### INSERISCI QUI SOTTO IL NOME DELLA CARTELLA E SALVA ######
dir=""

if [[ ${#dir} -eq 0 ]]
    then 
        echo "Cartella non rimossa."
        echo "Premi invio!"
        read
        nano remove.sh
        exit
fi

echo "rimuovo la cartella..."

rm -rf $dir

echo "cartella rimossa"

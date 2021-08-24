#! /usr/bin/zsh

if ls -1qA ./bin/ | grep -q . then
    rm  ./bin/*
    echo "Cleaning completed :D"
else
    echo "All binary files are cleaned :P"
fi
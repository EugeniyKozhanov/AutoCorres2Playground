#!/bin/bash


xhost si:localuser:$USER
docker run --net=host --env DISPLAY=$DISPLAY -v /tmp/.X11-unix:/tmp/.X11-unix -v $HOME/.Xauthority:/home/BRiCk/.Xauthority -v ./examples:/home/ubuntu/playground/examples --user $(id -u):$(id -g) $@ --rm -it ghcr.io/eugeniykozhanov/ac2-play:latest

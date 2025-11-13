#!/bin/bash


xhost si:localuser:$USER
docker run --net=host --env DISPLAY=$DISPLAY -v /tmp/.X11-unix:/tmp/.X11-unix -v $HOME/.Xauthority:/home/ubuntu/.Xauthority -v ./examples:/home/ubuntu/playground/examples -v ./exodus:/home/ubuntu/playground/exodus --user $(id -u):$(id -g) $@ --rm -it ghcr.io/eugeniykozhanov/ac2-play:latest

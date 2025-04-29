# Jupyter kernel for DeltaQ

A customized Jupyter iHaskell kernel for use with the [deltaq](https://github.com/DeltaQ-SD/deltaq) tool.


## Running a Jupyter server using Nix

Launch Jupyter with the iHaskell kernel including the `deltaq` and `probability-polynomial` packages:

```bash
nix run
```

In fact, this Jupyter kernel can be launced without directly cloning this repository:

```bash
nix run github:functionally/deltaq-jupyter
```

## Docker


### Building a docker image using Nix

First build the image.

```console
$ nix build -o deltaq-jupyter-docker.tar.gz ".#docker"

$ docker load --quiet < deltaq-jupyter-docker.tar.gz
Loaded image: localhost/jupyter-deltaq:2mf9zcagms0isg5n94xsml34kj4bn42k
```


### Push to docker registry

You can push the image to a registry.

```bash
docker push localhost/jupyter-deltaq:2mf9zcagms0isg5n94xsml34kj4bn42k \
            docker.io/bwbush/jupyter-deltaq:2mf9zcagms0isg5n94xsml34kj4bn42k
```


### Run the server in docker.

You can run the local image, exposing the service on port 9999 for example. The container should have at least 4 GB of memory and two CPUs, but larger computations require more memory. If you deploy this on kubernetes, you can use the HTTP path `/api` as the health check.

Locally, 

```bash
docker run --publish 9999:8888 localhost/jupyter-deltaq:2mf9zcagms0isg5n94xsml34kj4bn42k
```

or from DockerHub,

```bash
docker run --publish 9999:8888 ghcr.io/functionally/deltaq-jupyter:latest
```

The default password is `deltaq`: you can change this by visiting http://localhost:9999/lab in a web browser. Alternatively, you can use with the default password by visiting http://localhost:9999/lab?token=deltaq.

Use the "upload" and "download" features to move notebooks in and out of the container.


## Updates

In order to use the latest version of the `deltaq` packages, update the nix flake.

```bash
nix flake lock --update-input deltaq 
```

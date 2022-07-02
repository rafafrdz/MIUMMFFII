# A Docker container with SWI-Prolog
This deployment is served for those people who don't want to install SWI-Prolog in their laptop and prefer just launch a docker container.

## Pre-requisites
- To have installed `docker` and `docker-compose`
## How to install
First of all, you have to build the docker image. Alocate in the folder docker (where the `Dockerfile` is cointained) and execute:

```docker
docker build -t <username>/<image-name>

# For instance
docker build -t rafafrdz/swi-prolog
```

Once you have build the docker image, you can deploy it executing either

```docker
docker run -it rafafrdz/swipl-prolog
```
or if you prefere by `docker-compose` execute the service **prolog** contained into the `docker-compose.yml`

```docker
docker-compose run --rm prolog
```
if you set `--rm` then the docker will be eliminated when you close the SWI-Prolog console.

### Execute SWI-Prolog by docker in any path

You can execute the command that deploy a docker with SWI-Prolog in any path: You have to do the following:
- Create a new file, for instance, `prolog` or `prolog.sh`
- Execute `chmod +777 prolog.sh`
- Write into that file the script shown below:

```bash
docker-compose -f /path/subpath/docker-compose.yml run --rm prolog
```
- And finally, add the path where the script is alocated to the **PATH** variable.

Personally, I prefer without the .sh extension because in this way it seems a bash command.
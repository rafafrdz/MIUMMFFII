docker build -t rafafrdz/swipl-prolog
docker run -it rafafrdz/swipl-prolog
docker-compose run --rm prolog /bin/bash

-- run prolog
docker-compose run --rm prolog

-- run prolog from any path
docker-compose -f /mnt/d/git/MetodosFormales/TFM/Prolog/docker/docker-compose.yml run --rm prolog

add a script sh without extension .sh in some path that PATH variable contains.
that script has to contain the docker method described above.
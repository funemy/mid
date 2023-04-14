FROM haskell:9.0.2

WORKDIR /project
COPY stack.yaml .
COPY stack.yaml.lock .
ADD mid mid

RUN stack build

# ENTRYPOINT ["/bin/bash"]
ENTRYPOINT ["stack", "ghci", "mid/src/Example.hs"]
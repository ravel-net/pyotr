sudo docker pull batfish/allinone
python3 -m pip install --upgrade pybatfish
pip3 install networkx[default]
sudo docker run --name batfish -v batfish-data:/data -p 8888:8888 -p 9997:9997 -p 9996:9996 batfish/allinone


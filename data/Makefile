.PHONY: all clean

all: disneyland_paris_ways_and_nodes.json

disneyland_paris_ways_and_nodes.json:
	@echo "Fetching ways and their nodes in Disneyland Paris..."
	@curl -s -X POST https://overpass-api.de/api/interpreter \
	  -H "Content-Type: application/x-www-form-urlencoded" \
	  --data-urlencode "data=[out:json][timeout:60];area[\"name\"=\"Disneyland Paris\"]->.a;(way(area.a););(._;>;);out body;" \
	  -o $@
	@echo "Data saved to $@"

clean:
	@echo "Cleaning up..."
	@rm -f disneyland_paris_ways_and_nodes.json

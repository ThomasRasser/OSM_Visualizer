.PHONY: all clean disneyland prater europapark

all: clean disneyland_paris.json prater_vienna.json familypark_neusiedlersee.json

disneyland_paris.json:
	@echo "Fetching Disneyland (Paris) data..."
	@curl -s -X POST https://overpass-api.de/api/interpreter \
	  -H "Content-Type: application/x-www-form-urlencoded" \
	  --data-urlencode "data=[out:json][timeout:60];area[\"name\"=\"Disneyland Paris\"]->.a;(way(area.a););(._;>;);out body;" \
	  -o $@
	@echo "Saved to $@"

prater_vienna.json:
	@echo "Fetching Prater (Vienna) data..."
	@curl -s -X POST https://overpass-api.de/api/interpreter \
	  -H "Content-Type: application/x-www-form-urlencoded" \
	  --data-urlencode "data=[out:json][timeout:60];area[\"name\"=\"Wurstelprater\"]->.a;(way(area.a););(._;>;);out body;" \
	  -o $@
	@echo "Saved to $@"

familypark_neusiedlersee.json:
	@echo "Fetching Familypark (Neusiedlersee) data..."
	@curl -s -X POST https://overpass-api.de/api/interpreter \
	  -H "Content-Type: application/x-www-form-urlencoded" \
	  --data-urlencode "data=[out:json][timeout:60];area[\"name\"=\"Familypark Neusiedlersee\"]->.a;(way(area.a););(._;>;);out body;" \
	  -o $@
	@echo "Saved to $@"

clean:
	@echo "Cleaning up..."
	@rm -f disneyland_paris.json prater_vienna.json

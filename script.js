// Variable to store OSM data
let osmData = null;

// DOM elements
const canvas = document.getElementById('mapCanvas');
const ctx = canvas.getContext('2d');
const nodeDataDisplay = document.getElementById('nodeData');
const tagFiltersContainer = document.getElementById('tagFilters');
const tagValuesContainer = document.getElementById('tagValues');
const nodeSizeValue = document.getElementById('nodeSizeValue');
const nodeSizeIncrease = document.getElementById('nodeSizeIncrease');
const nodeSizeDecrease = document.getElementById('nodeSizeDecrease');
const nodeColorPicker = document.getElementById('nodeColor');
const wayColorPicker = document.getElementById('wayColor');
const wayWidthValue = document.getElementById('wayWidthValue');
const wayWidthIncrease = document.getElementById('wayWidthIncrease');
const wayWidthDecrease = document.getElementById('wayWidthDecrease');
const showLabelsCheckbox = document.getElementById('showLabels');
const resetViewButton = document.getElementById('resetView');
const enableAllFiltersButton = document.getElementById('enableAllFilters');
const disableAllFiltersButton = document.getElementById('disableAllFilters');
const dataFileSelector = document.getElementById('dataFile');
const loadingIndicator = document.getElementById('loadingIndicator');
const loadingText = document.getElementById('loadingText');
const globalFilterSearch = document.getElementById('globalFilterSearch');
const globalSearchResults = document.getElementById('globalSearchResults');

// App state
let nodeSize = 2;
let nodeColor = '#ff0000';
let wayColor = '#0000ff';
let wayWidth = 2;
let showLabels = true;
let activeFilters = {};
let activeFilterValues = {}; // Store values for active filters
let hoveredElement = null;
let selectedElement = null;
let nodes = [];
let ways = [];
let currentDataFile = 'data/disneyland_paris.json'; // Default data file

// Map calculations
let minLat = Infinity, maxLat = -Infinity;
let minLon = Infinity, maxLon = -Infinity;
let mapPadding = 50;
let nodeMap = {}; // Map of node id to node object for quick lookup

// For spatial querying - we'll use a quadtree-like approach
let spatialGrid = {};
const GRID_CELL_SIZE = 50; // Size of each grid cell in pixels

// For caching screen coordinates
let screenCoords = {};

// For throttling intensive operations
let lastDrawTime = 0;
const DRAW_THROTTLE = 16; // ~60fps

// Animation frame ID for rendering
let renderFrameId = null;

// Function to convert latitude and longitude to screen coordinates while preserving proportions
function convertToScreenCoords(lat, lon, canvasWidth, canvasHeight) {
  // Check if we already have this coordinate cached
  const key = `${lat},${lon},${canvasWidth},${canvasHeight}`;
  if (screenCoords[key]) {
    return screenCoords[key];
  }

  // Calculate the aspect ratio of the data
  const dataWidth = maxLon - minLon;
  const dataHeight = maxLat - minLat;
  const dataAspectRatio = dataWidth / dataHeight;

  // Calculate the aspect ratio of the canvas (minus padding)
  const effectiveCanvasWidth = canvasWidth - (mapPadding * 2);
  const effectiveCanvasHeight = canvasHeight - (mapPadding * 2);
  const canvasAspectRatio = effectiveCanvasWidth / effectiveCanvasHeight;

  let scaledWidth, scaledHeight, offsetX, offsetY;

  // Determine which dimension constrains the scaling
  if (dataAspectRatio > canvasAspectRatio) {
    // Data is wider than canvas (relative to height)
    // Use width as constraint
    scaledWidth = effectiveCanvasWidth;
    scaledHeight = scaledWidth / dataAspectRatio;
    offsetX = mapPadding;
    offsetY = mapPadding + (effectiveCanvasHeight - scaledHeight) / 2;
  } else {
    // Data is taller than canvas (relative to width)
    // Use height as constraint
    scaledHeight = effectiveCanvasHeight;
    scaledWidth = scaledHeight * dataAspectRatio;
    offsetX = mapPadding + (effectiveCanvasWidth - scaledWidth) / 2;
    offsetY = mapPadding;
  }

  // Convert coordinates with proper scaling and centering
  const x = offsetX + ((lon - minLon) / dataWidth) * scaledWidth;
  const y = canvasHeight - (offsetY + ((lat - minLat) / dataHeight) * scaledHeight);

  // Cache the result
  screenCoords[key] = { x, y };

  return { x, y };
}

// Function to create a map of node IDs to node objects for quick lookup
function createNodeMap() {
  nodeMap = {};
  nodes.forEach(node => {
    nodeMap[node.id] = node;
  });
}

// Function to build a spatial index for nodes to improve hit detection
function buildSpatialIndex() {
  spatialGrid = {};

  const canvasWidth = canvas.width;
  const canvasHeight = canvas.height;

  // Add nodes to spatial grid
  nodes.forEach(node => {
    const coords = convertToScreenCoords(node.lat, node.lon, canvasWidth, canvasHeight);
    const gridX = Math.floor(coords.x / GRID_CELL_SIZE);
    const gridY = Math.floor(coords.y / GRID_CELL_SIZE);

    const cellKey = `${gridX},${gridY}`;
    if (!spatialGrid[cellKey]) {
      spatialGrid[cellKey] = { nodes: [], ways: [] };
    }

    spatialGrid[cellKey].nodes.push(node);
  });

  // Add ways to spatial grid (based on each node in the way)
  ways.forEach(way => {
    if (!way.nodes || way.nodes.length < 2) return;

    const wayCells = new Set(); // Track cells this way passes through

    for (let i = 0; i < way.nodes.length - 1; i++) {
      const nodeA = nodeMap[way.nodes[i]];
      const nodeB = nodeMap[way.nodes[i + 1]];

      if (!nodeA || !nodeB) continue;

      const coordsA = convertToScreenCoords(nodeA.lat, nodeA.lon, canvasWidth, canvasHeight);
      const coordsB = convertToScreenCoords(nodeB.lat, nodeB.lon, canvasWidth, canvasHeight);

      // Get all cells this line segment passes through (Bresenham-like approach)
      const cellsOnPath = getCellsOnLinePath(coordsA.x, coordsA.y, coordsB.x, coordsB.y);

      cellsOnPath.forEach(cell => {
        wayCells.add(cell);
      });
    }

    // Add the way to all cells it passes through
    wayCells.forEach(cellKey => {
      if (!spatialGrid[cellKey]) {
        spatialGrid[cellKey] = { nodes: [], ways: [] };
      }
      spatialGrid[cellKey].ways.push(way);
    });
  });
}

// Get cells that a line segment passes through
function getCellsOnLinePath(x1, y1, x2, y2) {
  const cells = new Set();

  // Get starting and ending grid cells
  const startGridX = Math.floor(x1 / GRID_CELL_SIZE);
  const startGridY = Math.floor(y1 / GRID_CELL_SIZE);
  const endGridX = Math.floor(x2 / GRID_CELL_SIZE);
  const endGridY = Math.floor(y2 / GRID_CELL_SIZE);

  // Add the start and end cells
  cells.add(`${startGridX},${startGridY}`);
  cells.add(`${endGridX},${endGridY}`);

  // For short segments, this is enough
  if (Math.abs(startGridX - endGridX) <= 1 && Math.abs(startGridY - endGridY) <= 1) {
    return Array.from(cells);
  }

  // For longer segments, sample points along the line
  const dx = x2 - x1;
  const dy = y2 - y1;
  const steps = Math.max(Math.abs(dx), Math.abs(dy)) / (GRID_CELL_SIZE / 2);

  for (let i = 1; i < steps; i++) {
    const t = i / steps;
    const x = x1 + dx * t;
    const y = y1 + dy * t;

    const gridX = Math.floor(x / GRID_CELL_SIZE);
    const gridY = Math.floor(y / GRID_CELL_SIZE);

    cells.add(`${gridX},${gridY}`);
  }

  return Array.from(cells);
}

// Function to get nearby elements based on spatial index
function getElementsNearPoint(x, y) {
  const gridX = Math.floor(x / GRID_CELL_SIZE);
  const gridY = Math.floor(y / GRID_CELL_SIZE);

  const nearbyElements = {
    nodes: [],
    ways: []
  };

  // Check the grid cell and 8 surrounding cells
  for (let i = -1; i <= 1; i++) {
    for (let j = -1; j <= 1; j++) {
      const cellKey = `${gridX + i},${gridY + j}`;
      if (spatialGrid[cellKey]) {
        nearbyElements.nodes.push(...spatialGrid[cellKey].nodes);
        nearbyElements.ways.push(...spatialGrid[cellKey].ways);
      }
    }
  }

  return nearbyElements;
}

// Function to draw the map with offscreen canvas rendering
function drawMap() {
  const now = performance.now();
  if (now - lastDrawTime < DRAW_THROTTLE && renderFrameId) {
    return; // Skip this frame if we're throttling
  }

  // Cancel any previous render frame
  if (renderFrameId) {
    cancelAnimationFrame(renderFrameId);
  }

  // Schedule the render on the next animation frame
  renderFrameId = requestAnimationFrame(() => {
    lastDrawTime = performance.now();
    renderFrameId = null;

    // Set canvas size if needed
    if (canvas.width !== canvas.parentElement.clientWidth ||
        canvas.height !== canvas.parentElement.clientHeight) {
      canvas.width = canvas.parentElement.clientWidth;
      canvas.height = canvas.parentElement.clientHeight;

      // Clear coordinate cache when canvas size changes
      screenCoords = {};

      // Rebuild spatial index when canvas size changes
      buildSpatialIndex();
    }

    // Create offscreen canvas for better performance
    const offscreenCanvas = document.createElement('canvas');
    offscreenCanvas.width = canvas.width;
    offscreenCanvas.height = canvas.height;
    const offCtx = offscreenCanvas.getContext('2d');

    // Clear canvas
    offCtx.clearRect(0, 0, offscreenCanvas.width, offscreenCanvas.height);

    // Use filter check only once per way
    const filteredWays = ways.filter(shouldDisplayNode);

    // Draw ways first (so they appear behind nodes)
    for (const way of filteredWays) {
      drawWay(way, offCtx);
    }

    // Use filter check only once per node
    const filteredNodes = nodes.filter(shouldDisplayNode);

    // Draw nodes in batches to improve performance
    const nodeBatchSize = 1000;
    for (let i = 0; i < filteredNodes.length; i += nodeBatchSize) {
      const batch = filteredNodes.slice(i, i + nodeBatchSize);
      drawNodeBatch(batch, offCtx);
    }

    // Copy the offscreen canvas to the visible canvas
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.drawImage(offscreenCanvas, 0, 0);
  });
}

// Function to draw a batch of nodes for better performance
function drawNodeBatch(nodeBatch, ctx) {
  for (const node of nodeBatch) {
    const coords = convertToScreenCoords(node.lat, node.lon, canvas.width, canvas.height);
    const isHovered = hoveredElement && hoveredElement.id === node.id && hoveredElement.type === 'node';
    const isSelected = selectedElement && selectedElement.id === node.id && selectedElement.type === 'node';

    // Draw node with different size/color if hovered or selected
    ctx.beginPath();
    if (isSelected) {
      ctx.fillStyle = '#00ff00'; // Highlight color for selected node
      ctx.arc(coords.x, coords.y, nodeSize * 1.5, 0, Math.PI * 2); // Bigger when selected
    } else if (isHovered) {
      ctx.fillStyle = '#00aaff'; // Lighter blue for hovered node
      ctx.arc(coords.x, coords.y, nodeSize * 1.2, 0, Math.PI * 2); // Slightly bigger when hovered
    } else {
      ctx.fillStyle = nodeColor;
      ctx.arc(coords.x, coords.y, nodeSize, 0, Math.PI * 2);
    }
    ctx.fill();

    // Draw label if enabled and node has a name
    if ((showLabels || isSelected) && node.tags && node.tags.name) {
      ctx.fillStyle = '#000';
      ctx.font = '12px Arial';
      ctx.textAlign = 'center';
      ctx.fillText(node.tags.name, coords.x, coords.y - nodeSize - 5);
    }
  }
}

// Function to draw a way (line connecting nodes)
function drawWay(way, ctx) {
  if (!way.nodes || way.nodes.length < 2) return;

  // Start a new path
  ctx.beginPath();

  // Set way style
  const isHovered = hoveredElement && hoveredElement.id === way.id && hoveredElement.type === 'way';
  const isSelected = selectedElement && selectedElement.id === way.id && selectedElement.type === 'way';

  if (isSelected) {
    ctx.strokeStyle = '#00ff00'; // Highlight color for selected way
    ctx.lineWidth = wayWidth * 1.5; // Wider when selected
  } else if (isHovered) {
    ctx.strokeStyle = '#00aaff'; // Lighter blue for hovered way
    ctx.lineWidth = wayWidth * 1.2; // Slightly wider when hovered
  } else {
    ctx.strokeStyle = wayColor;
    ctx.lineWidth = wayWidth;
  }

  let firstNodeDrawn = false;
  const canvasWidth = canvas.width;
  const canvasHeight = canvas.height;

  // Draw lines between nodes
  for (const nodeId of way.nodes) {
    const node = nodeMap[nodeId];

    // Skip if node doesn't exist
    if (!node) continue;

    const coords = convertToScreenCoords(node.lat, node.lon, canvasWidth, canvasHeight);

    if (!firstNodeDrawn) {
      ctx.moveTo(coords.x, coords.y);
      firstNodeDrawn = true;
    } else {
      ctx.lineTo(coords.x, coords.y);
    }
  }

  // Stroke the path
  ctx.stroke();
}

// Function to check if a node should be displayed based on active filters (optimized)
function shouldDisplayNode(node) {
  // If no filters are active, show all nodes
  if (Object.keys(activeFilters).length === 0) return true;

  // If node has no tags, only show it if no tag filters are active
  if (!node.tags) return false;

  // Create a one-time cache of active filter keys for better performance
  const activeFilterKeys = Object.keys(activeFilters).filter(key => activeFilters[key]);
  if (activeFilterKeys.length === 0) return true;

  // Get active filter values
  const activeValueKeys = Object.keys(activeFilterValues).filter(key =>
    Object.values(activeFilterValues[key]).some(value => value)
  );

  // No active value filters, just check the tags
  if (activeValueKeys.length === 0) {
    // Check if node has at least one of the active tag filters
    for (const tag of activeFilterKeys) {
      if (node.tags[tag]) return true;
    }
  } else {
    // Check if node has active tag AND its value is selected
    for (const tag of activeFilterKeys) {
      if (node.tags[tag]) {
        // If tag is in active value filters, check if value is selected
        if (activeValueKeys.includes(tag)) {
          const value = node.tags[tag];
          if (activeFilterValues[tag][value]) return true;
        } else {
          // Tag is active but no value filtering
          return true;
        }
      }
    }
  }

  return false;
}

// Debounce function to limit how often an expensive function can be called
function debounce(func, wait) {
  let timeout;
  return function(...args) {
    const context = this;
    clearTimeout(timeout);
    timeout = setTimeout(() => func.apply(context, args), wait);
  };
}

// Throttle function to limit the rate at which a function can fire
function throttle(func, limit) {
  let inThrottle;
  return function(...args) {
    const context = this;
    if (!inThrottle) {
      func.apply(context, args);
      inThrottle = true;
      setTimeout(() => inThrottle = false, limit);
    }
  };
}

// Function to handle mouse movement for element hovering (optimized)
const handleMouseMove = throttle(function(e) {
  const rect = canvas.getBoundingClientRect();
  const mouseX = e.clientX - rect.left;
  const mouseY = e.clientY - rect.top;

  const previousHoveredElement = hoveredElement;
  hoveredElement = null;

  // Get nearby elements using spatial index
  const nearbyElements = getElementsNearPoint(mouseX, mouseY);

  // Check for nodes first (higher priority for hovering)
  for (const node of nearbyElements.nodes) {
    if (!shouldDisplayNode(node)) continue;

    const coords = convertToScreenCoords(node.lat, node.lon, canvas.width, canvas.height);
    const distance = Math.sqrt(Math.pow(mouseX - coords.x, 2) + Math.pow(mouseY - coords.y, 2));

    if (distance <= nodeSize * 1.5) { // Slightly larger hover area
      hoveredElement = node;
      hoveredElement.type = 'node'; // Ensure type is set
      canvas.style.cursor = 'pointer';
      break;
    }
  }

  // If no node found, check for ways
  if (!hoveredElement) {
    for (const way of nearbyElements.ways) {
      if (!shouldDisplayNode(way)) continue;

      // Check if mouse is near any segment of the way
      if (isMouseNearWay(way, mouseX, mouseY)) {
        hoveredElement = way;
        hoveredElement.type = 'way'; // Ensure type is set
        canvas.style.cursor = 'pointer';
        break;
      }
    }
  }

  // Reset cursor if no element is hovered
  if (!hoveredElement) {
    canvas.style.cursor = 'default';
  }

  // Only redraw if the hovered element changed
  if (previousHoveredElement !== hoveredElement) {
    drawMap();
  }
}, 30); // Throttle to 30ms (about 33fps) to prevent excessive processing

// Function to handle mouse clicks for element selection
function handleMouseClick(e) {
  // If we have a hovered element when clicked, select it
  if (hoveredElement) {
    if (selectedElement === hoveredElement) {
      // If clicking the already selected element, deselect it
      selectedElement = null;
    } else {
      // Otherwise, select the hovered element
      selectedElement = hoveredElement;

      // Update data display
      nodeDataDisplay.textContent = JSON.stringify(selectedElement, null, 2);
    }

    // Redraw to update the selection visuals
    drawMap();
  } else {
    // If clicking on empty space, deselect any selected element
    if (selectedElement) {
      selectedElement = null;
      nodeDataDisplay.textContent = 'Click on a node or way to see its data';
      drawMap();
    }
  }
}

// Function to check if mouse is near a way (optimized)
function isMouseNearWay(way, mouseX, mouseY) {
  if (!way.nodes || way.nodes.length < 2) return false;

  // Threshold distance from line segment
  const threshold = wayWidth * 2;

  // Check each segment of the way
  for (let i = 0; i < way.nodes.length - 1; i++) {
    const nodeA = nodeMap[way.nodes[i]];
    const nodeB = nodeMap[way.nodes[i + 1]];

    // Skip if either node doesn't exist
    if (!nodeA || !nodeB) continue;

    const coordsA = convertToScreenCoords(nodeA.lat, nodeA.lon, canvas.width, canvas.height);
    const coordsB = convertToScreenCoords(nodeB.lat, nodeB.lon, canvas.width, canvas.height);

    // Calculate distance from point to line segment
    const distance = distanceToLineSegment(
      mouseX, mouseY,
      coordsA.x, coordsA.y,
      coordsB.x, coordsB.y
    );

    if (distance <= threshold) {
      return true;
    }
  }

  return false;
}

// Calculate distance from point to line segment (optimized)
function distanceToLineSegment(px, py, x1, y1, x2, y2) {
  const A = px - x1;
  const B = py - y1;
  const C = x2 - x1;
  const D = y2 - y1;

  const dot = A * C + B * D;
  const lenSq = C * C + D * D;
  let param = -1;

  if (lenSq !== 0) { // in case of 0 length line
    param = dot / lenSq;
  }

  let xx, yy;

  if (param < 0) {
    xx = x1;
    yy = y1;
  } else if (param > 1) {
    xx = x2;
    yy = y2;
  } else {
    xx = x1 + param * C;
    yy = y1 + param * D;
  }

  const dx = px - xx;
  const dy = py - yy;

  return Math.sqrt(dx * dx + dy * dy);
}

// Function to extract unique tags from nodes with counts (optimized with worker)
function extractUniqueTags() {
  // Use memoization for this expensive operation
  if (extractUniqueTags.cache) {
    return extractUniqueTags.cache;
  }

  console.time('Extract tags');

  const tagCounts = {};

  // Process nodes and ways in chunks for better performance
  const processElements = (elements, startIdx, endIdx) => {
    for (let i = startIdx; i < endIdx && i < elements.length; i++) {
      const element = elements[i];
      if (element.tags) {
        for (const tag in element.tags) {
          if (!tagCounts[tag]) {
            tagCounts[tag] = 0;
          }
          tagCounts[tag]++;
        }
      }
    }
  };

  const CHUNK_SIZE = 5000;

  // Process nodes in chunks
  for (let i = 0; i < nodes.length; i += CHUNK_SIZE) {
    processElements(nodes, i, i + CHUNK_SIZE);
  }

  // Process ways in chunks
  for (let i = 0; i < ways.length; i += CHUNK_SIZE) {
    processElements(ways, i, i + CHUNK_SIZE);
  }

  // Convert to array of objects with tag name and count
  const tagsWithCounts = Object.entries(tagCounts).map(([tag, count]) => ({
    tag,
    count
  }));

  // Sort by count (descending)
  tagsWithCounts.sort((a, b) => b.count - a.count);

  console.timeEnd('Extract tags');

  // Cache the result
  extractUniqueTags.cache = tagsWithCounts;

  return tagsWithCounts;
}

// Function to extract unique values for a tag
function extractTagValues(tag) {
  const values = {};
  let totalCount = 0;

  // Collect all values for this tag
  [...nodes, ...ways].forEach(element => {
    if (element.tags && element.tags[tag]) {
      const value = element.tags[tag];
      if (!values[value]) {
        values[value] = {
          value,
          count: 0
        };
      }
      values[value].count++;
      totalCount++;
    }
  });

  // Convert to array
  const valuesArray = Object.values(values);

  // Sort by count
  valuesArray.sort((a, b) => b.count - a.count);

  return { values: valuesArray, totalCount };
}

// Function to create tag value filters
function createTagValueFilters() {
  // Clear existing values
  tagValuesContainer.innerHTML = '';

  // Get active filter keys
  const activeFilterKeys = Object.keys(activeFilters).filter(key => activeFilters[key]);

  // Show/hide global search based on active filters
  const globalSearchContainer = document.querySelector('.global-filter-search');
  if (activeFilterKeys.length === 0) {
    tagValuesContainer.innerHTML = '<div class="filter-info">Select a tag filter to see values</div>';
    globalSearchContainer.style.display = 'none';
    return;
  } else {
    globalSearchContainer.style.display = 'block';
  }

  // Set up global search if not already done
  if (!globalFilterSearch._hasEventListener) {
    globalFilterSearch.addEventListener('input', (e) => {
      const searchValue = e.target.value.trim().toLowerCase();

      // Apply filter to all tag sections
      const allTagSections = tagValuesContainer.querySelectorAll('.filter-tag-section');

      allTagSections.forEach(section => {
        const valueElements = section.querySelectorAll('.filter-value');
        let visibleCount = 0;

        valueElements.forEach(el => {
          const labelText = el.querySelector('label').textContent.toLowerCase();
          if (searchValue === '' || labelText.includes(searchValue)) {
            el.style.display = '';
            visibleCount++;
          } else {
            el.style.display = 'none';
          }
        });

        // Hide entire section if no matching values
        if (visibleCount === 0) {
          section.style.display = 'none';
        } else {
          section.style.display = '';
        }

        // Also reset the individual search input for this section
        const sectionSearchInput = section.querySelector('.filter-search-input');
        if (sectionSearchInput && searchValue) {
          sectionSearchInput.value = '';
        }
      });

      // Show a message if all sections are hidden
      const visibleSections = tagValuesContainer.querySelectorAll('.filter-tag-section[style=""]');
      if (visibleSections.length === 0 && searchValue !== '') {
        // Check if we already have a no-results message
        let noResultsMsg = tagValuesContainer.querySelector('.global-no-results');
        if (!noResultsMsg) {
          noResultsMsg = document.createElement('div');
          noResultsMsg.className = 'global-no-results';
          noResultsMsg.textContent = 'No matching values found in any filter';
          tagValuesContainer.appendChild(noResultsMsg);
        } else {
          noResultsMsg.style.display = '';
        }
      } else {
        // Hide the no-results message if we have visible sections
        const noResultsMsg = tagValuesContainer.querySelector('.global-no-results');
        if (noResultsMsg) {
          noResultsMsg.style.display = 'none';
        }
      }
    });

    // Mark that we've added the event listener
    globalFilterSearch._hasEventListener = true;
  }

  // Use DocumentFragment for better performance
  const fragment = document.createDocumentFragment();

  // For each active tag, show its values
  activeFilterKeys.forEach(tag => {
    // Get values for this tag
    const { values, totalCount } = extractTagValues(tag);

    // Skip tags with no values
    if (values.length === 0) {
      return;
    }

    const tagSection = document.createElement('div');
    tagSection.className = 'filter-tag-section';

    const tagHeader = document.createElement('div');
    tagHeader.className = 'filter-tag-header';
    tagHeader.textContent = tag;
    tagSection.appendChild(tagHeader);

    // Add search input for this tag
    const searchContainer = document.createElement('div');
    searchContainer.className = 'filter-search-container';

    const searchInput = document.createElement('input');
    searchInput.type = 'text';
    searchInput.placeholder = 'Search values...';
    searchInput.className = 'filter-search-input';
    searchInput.dataset.tag = tag; // Store the tag this search is for

    searchInput.addEventListener('input', (e) => {
      const searchValue = e.target.value.toLowerCase();
      const valueElements = tagSection.querySelectorAll('.filter-value');

      let visibleCount = 0;
      valueElements.forEach(el => {
        const labelText = el.querySelector('label').textContent.toLowerCase();
        if (searchValue === '' || labelText.includes(searchValue)) {
          el.style.display = '';
          visibleCount++;
        } else {
          el.style.display = 'none';
        }
      });

      // Clear the global search when using individual search
      if (searchValue) {
        globalFilterSearch.value = '';
      }
    });

    searchContainer.appendChild(searchInput);
    tagSection.appendChild(searchContainer);

    // Initialize if not exists
    if (!activeFilterValues[tag]) {
      activeFilterValues[tag] = {};
    }

    // Create value filters
    const valuesContainer = document.createElement('div');
    valuesContainer.className = 'filter-values-list';

    // Show all values, we'll make it scrollable
    values.forEach(({ value, count }) => {
      const valueContainer = document.createElement('div');
      valueContainer.className = 'filter-value';

      const checkbox = document.createElement('input');
      checkbox.type = 'checkbox';
      checkbox.id = `filter-${tag}-${value}`;
      checkbox.checked = activeFilterValues[tag][value] || false;

      checkbox.addEventListener('change', () => {
        // Update active filter values
        activeFilterValues[tag][value] = checkbox.checked;

        // Clear cache
        shouldDisplayNode.cache = {};
        drawMap();
      });

      const label = document.createElement('label');
      label.htmlFor = `filter-${tag}-${value}`;
      label.textContent = `${value} (${count})`;

      valueContainer.appendChild(checkbox);
      valueContainer.appendChild(label);
      valuesContainer.appendChild(valueContainer);
    });

    // Show total count
    if (values.length > 0) {
      const infoText = document.createElement('div');
      infoText.className = 'filter-value-count';
      infoText.textContent = `${values.length} unique values`;
      searchContainer.appendChild(infoText);
    }

    tagSection.appendChild(valuesContainer);
    fragment.appendChild(tagSection);
  });

  // Add all sections
  tagValuesContainer.appendChild(fragment);
}

// Function to toggle all filters
function toggleAllFilters(enable) {
  const tagsWithCounts = extractUniqueTags();

  tagsWithCounts.forEach(({ tag }) => {
    activeFilters[tag] = enable;

    // Update checkbox states
    const checkbox = document.getElementById(`filter-${tag}`);
    if (checkbox) {
      checkbox.checked = enable;
    }
  });

  // Clear value filters if disabling all
  if (!enable) {
    activeFilterValues = {};
  }

  // Clear cache
  shouldDisplayNode.cache = {};

  // Update value filters
  createTagValueFilters();

  // Redraw
  drawMap();
}

// Function to create tag filters (optimized)
const createTagFilters = debounce(function() {
  console.time('Create filters');

  const tagsWithCounts = extractUniqueTags();

  // Create filter header with search
  const filterHeader = document.createElement('div');
  filterHeader.className = 'filter-header';

  const searchContainer = document.createElement('div');
  searchContainer.className = 'filter-search-container';

  const searchInput = document.createElement('input');
  searchInput.type = 'text';
  searchInput.placeholder = 'Search filters...';
  searchInput.className = 'filter-search-input';

  searchInput.addEventListener('input', (e) => {
    const searchValue = e.target.value.toLowerCase();
    const filterElements = tagFiltersContainer.querySelectorAll('.filter-tag');

    filterElements.forEach(el => {
      const labelText = el.querySelector('label').textContent.toLowerCase();
      if (searchValue === '' || labelText.includes(searchValue)) {
        el.style.display = '';
      } else {
        el.style.display = 'none';
      }
    });
  });

  const filterCount = document.createElement('div');
  filterCount.className = 'filter-value-count';
  filterCount.textContent = `${tagsWithCounts.length} filters`;

  searchContainer.appendChild(searchInput);
  searchContainer.appendChild(filterCount);
  filterHeader.appendChild(searchContainer);

  // Clear and add the header
  tagFiltersContainer.innerHTML = '';
  tagFiltersContainer.appendChild(filterHeader);

  // Use DocumentFragment for better performance
  const fragment = document.createDocumentFragment();

  // Create a div to contain just the filter tags (for better scrolling)
  const filterTagsContainer = document.createElement('div');
  filterTagsContainer.className = 'filter-tags-list';

  tagsWithCounts.forEach(({ tag, count }) => {
    const filterContainer = document.createElement('div');
    filterContainer.className = 'filter-tag';

    const checkbox = document.createElement('input');
    checkbox.type = 'checkbox';
    checkbox.id = `filter-${tag}`;
    checkbox.checked = activeFilters[tag] || false;

    checkbox.addEventListener('change', () => {
      activeFilters[tag] = checkbox.checked;

      if (!checkbox.checked) {
        // Remove tag from active filter values
        delete activeFilterValues[tag];
      }

      if (Object.values(activeFilters).every(v => !v)) {
        // If all filters are unchecked, clear active filters
        activeFilters = {};
        activeFilterValues = {};
      }

      // Update value filters
      createTagValueFilters();

      // Clear cache when filters change
      shouldDisplayNode.cache = {};
      drawMap();
    });

    const label = document.createElement('label');
    label.htmlFor = `filter-${tag}`;
    label.textContent = `${tag} (${count})`;

    filterContainer.appendChild(checkbox);
    filterContainer.appendChild(label);
    filterTagsContainer.appendChild(filterContainer);
  });

  fragment.appendChild(filterTagsContainer);

  // Add fragment to container
  tagFiltersContainer.appendChild(fragment);

  // Update value filters
  createTagValueFilters();

  console.timeEnd('Create filters');
}, 300);

// Function to load the OSM data from file with progress feedback
async function loadOsmData(dataFile) {
  try {
    console.time('Data load');

    // Show loading state
    loadingIndicator.classList.add('active');
    loadingText.textContent = 'Loading...';
    nodeDataDisplay.textContent = 'Loading data...';

    // Reset state for new data
    nodes = [];
    ways = [];
    nodeMap = {};
    spatialGrid = {};
    screenCoords = {};
    activeFilters = {};
    activeFilterValues = {};
    hoveredElement = null;
    selectedElement = null;
    extractUniqueTags.cache = null;

    const response = await fetch(dataFile);

    if (!response.ok) {
      throw new Error(`Failed to load data: ${response.status} ${response.statusText}`);
    }

    // Use streaming to handle large files better
    const reader = response.body.getReader();
    const contentLength = +response.headers.get('Content-Length');

    let receivedLength = 0;
    let chunks = [];

    while (true) {
      const { done, value } = await reader.read();

      if (done) {
        break;
      }

      chunks.push(value);
      receivedLength += value.length;

      // Report progress
      if (contentLength) {
        const percentComplete = Math.round((receivedLength / contentLength) * 100);
        loadingText.textContent = `Loading: ${percentComplete}%`;
        nodeDataDisplay.textContent = `Loading data: ${percentComplete}%`;
      }
    }

    // Combine chunks into a single Uint8Array
    let chunksAll = new Uint8Array(receivedLength);
    let position = 0;
    for (let chunk of chunks) {
      chunksAll.set(chunk, position);
      position += chunk.length;
    }

    // Convert to text
    const json = new TextDecoder("utf-8").decode(chunksAll);
    osmData = JSON.parse(json);

    console.time('Process data');
    loadingText.textContent = 'Processing...';
    nodeDataDisplay.textContent = 'Processing data...';

    // Process data in chunks using setTimeout to avoid blocking the UI
    setTimeout(() => {
      // Split elements into nodes and ways
      nodes = osmData.elements.filter(element => element.type === 'node');
      ways = osmData.elements.filter(element => element.type === 'way');

      // Create a node ID to node object map for quick lookup
      createNodeMap();

      // Calculate bounds for map display
      calculateBounds();

      // Create tag filters once data is loaded
      loadingText.textContent = 'Building filters...';
      createTagFilters();

      // Build spatial index
      setTimeout(() => {
        // Now build the spatial index for performance
        loadingText.textContent = 'Building spatial index...';
        nodeDataDisplay.textContent = 'Building spatial index...';

        // Reset coordinate cache
        screenCoords = {};

        // Draw the map
        setTimeout(() => {
          nodeDataDisplay.textContent = 'Click on a node or way to see its data';
          loadingIndicator.classList.remove('active');
          drawMap();

          // Build spatial index after initial render
          setTimeout(() => buildSpatialIndex(), 100);

          console.timeEnd('Process data');
          console.timeEnd('Data load');
        }, 10);
      }, 10);
    }, 10);

  } catch (error) {
    console.error('Error loading OSM data:', error);
    nodeDataDisplay.textContent = `Error loading data: ${error.message}`;
    loadingIndicator.classList.remove('active');
  }
}

// Function to calculate map bounds (optimized)
function calculateBounds() {
  console.time('Calculate bounds');

  minLat = Infinity;
  maxLat = -Infinity;
  minLon = Infinity;
  maxLon = -Infinity;

  // Process in batches for better performance
  const BATCH_SIZE = 10000;

  for (let i = 0; i < nodes.length; i += BATCH_SIZE) {
    const endIdx = Math.min(i + BATCH_SIZE, nodes.length);

    for (let j = i; j < endIdx; j++) {
      const node = nodes[j];
      minLat = Math.min(minLat, node.lat);
      maxLat = Math.max(maxLat, node.lat);
      minLon = Math.min(minLon, node.lon);
      maxLon = Math.max(maxLon, node.lon);
    }
  }

  console.timeEnd('Calculate bounds');
}

// Handle window resize with throttling
const handleResize = throttle(() => {
  // Clear coordinate cache when resizing
  screenCoords = {};
  drawMap();
}, 100);

// Initialize the application
function init() {
  // Set data file selector
  dataFileSelector.value = currentDataFile;

  // Load the data first
  loadOsmData(currentDataFile);

  // Set up event listeners
  canvas.addEventListener('mousemove', handleMouseMove);
  canvas.addEventListener('click', handleMouseClick);

  // Data file selector
  dataFileSelector.addEventListener('change', (e) => {
    currentDataFile = e.target.value;
    loadOsmData(currentDataFile);
  });

  // Node size buttons
  nodeSizeIncrease.addEventListener('click', () => {
    if (nodeSize < 10) {
      nodeSize += 1;
      nodeSizeValue.textContent = nodeSize;
      drawMap();
    }
  });

  nodeSizeDecrease.addEventListener('click', () => {
    if (nodeSize > 1) {
      nodeSize -= 1;
      nodeSizeValue.textContent = nodeSize;
      drawMap();
    }
  });

  // Way width buttons
  wayWidthIncrease.addEventListener('click', () => {
    if (wayWidth < 10) {
      wayWidth += 1;
      wayWidthValue.textContent = wayWidth;
      drawMap();
    }
  });

  wayWidthDecrease.addEventListener('click', () => {
    if (wayWidth > 1) {
      wayWidth -= 1;
      wayWidthValue.textContent = wayWidth;
      drawMap();
    }
  });

  nodeColorPicker.addEventListener('input', () => {
    nodeColor = nodeColorPicker.value;
    drawMap();
  });

  wayColorPicker.addEventListener('input', () => {
    wayColor = wayColorPicker.value;
    drawMap();
  });

  showLabelsCheckbox.addEventListener('change', () => {
    showLabels = showLabelsCheckbox.checked;
    drawMap();
  });

  resetViewButton.addEventListener('click', () => {
    nodeSize = 2;
    nodeColor = '#ff0000';
    wayColor = '#0000ff';
    wayWidth = 2;
    showLabels = true;
    activeFilters = {};
    activeFilterValues = {};

    // Clear caches
    screenCoords = {};
    extractUniqueTags.cache = null;
    shouldDisplayNode.cache = {};

    // Reset UI elements
    nodeSizeValue.textContent = nodeSize;
    nodeColorPicker.value = nodeColor;
    wayColorPicker.value = wayColor;
    wayWidthValue.textContent = wayWidth;
    showLabelsCheckbox.checked = showLabels;

    // Reset tag filters UI
    createTagFilters();
    drawMap();
  });

  // Enable/disable all filters buttons
  enableAllFiltersButton.addEventListener('click', () => {
    toggleAllFilters(true);
  });

  disableAllFiltersButton.addEventListener('click', () => {
    toggleAllFilters(false);
  });

  // Handle window resize
  window.addEventListener('resize', handleResize);
}

// Start the application when the DOM is ready
document.addEventListener('DOMContentLoaded', init);

const React = window.React;
const ReactDOM = window.ReactDOM;
const { useState, useRef, useCallback, useEffect, useMemo } = React;

// Browser-only static app (no Electron)

// Parse arc command parameters, correctly handling concatenated flag digits
// Arc has 7 params per arc: rx ry rotation largeArc sweep x y
// Flags (params 4 and 5) are single digits that can be written without separators
function parseArcParams(str) {
  str = str.replace(/,/g, ' ').trim();
  const result = [];
  let i = 0;
  let numCount = 0;
  
  while (i < str.length) {
    while (i < str.length && /\s/.test(str[i])) i++;
    if (i >= str.length) break;
    
    const paramIndex = numCount % 7;
    
    // Params 3 and 4 (0-indexed) are flags - take exactly one digit
    if (paramIndex === 3 || paramIndex === 4) {
      if (str[i] === '0' || str[i] === '1') {
        result.push(parseInt(str[i]));
        i++;
        numCount++;
        continue;
      }
    }
    
    // Regular number
    let numStr = '';
    if (str[i] === '-' || str[i] === '+') { numStr += str[i]; i++; }
    while (i < str.length && /\d/.test(str[i])) { numStr += str[i]; i++; }
    if (i < str.length && str[i] === '.') {
      numStr += str[i]; i++;
      while (i < str.length && /\d/.test(str[i])) { numStr += str[i]; i++; }
    }
    if (i < str.length && (str[i] === 'e' || str[i] === 'E')) {
      numStr += str[i]; i++;
      if (i < str.length && (str[i] === '-' || str[i] === '+')) { numStr += str[i]; i++; }
      while (i < str.length && /\d/.test(str[i])) { numStr += str[i]; i++; }
    }
    
    if (numStr) { result.push(parseFloat(numStr)); numCount++; }
  }
  return result;
}

// Split a self-intersecting polygon into separate non-intersecting contours
// This handles fill-rule paths where the polygon crosses itself to create holes
function splitSelfIntersectingPolygon(points) {
  if (!points || points.length < 4) return [points];
  
  const n = points.length;
  
  // Find all edge intersections
  const intersections = []; // {i, j, point, ti, tj} - edge i and j intersect at point
  
  for (let i = 0; i < n; i++) {
    const a1 = points[i];
    const a2 = points[(i + 1) % n];
    
    for (let j = i + 2; j < n; j++) {
      // Skip adjacent edges and wrap-around adjacency
      if (j === (i + n - 1) % n) continue;
      if (i === 0 && j === n - 1) continue;
      
      const b1 = points[j];
      const b2 = points[(j + 1) % n];
      
      const intersection = lineIntersection(a1, a2, b1, b2);
      if (intersection) {
        intersections.push({
          i: i,
          j: j,
          point: intersection.point,
          ti: intersection.t1,
          tj: intersection.t2
        });
      }
    }
  }
  
  // If no intersections, return original polygon
  if (intersections.length === 0) return [points];
  
  // Build a graph with original points and intersection points
  // Each edge can have multiple intersection points along it
  const edgeIntersections = Array(n).fill(null).map(() => []);
  
  for (const isect of intersections) {
    edgeIntersections[isect.i].push({ t: isect.ti, point: isect.point, otherEdge: isect.j, otherT: isect.tj });
    edgeIntersections[isect.j].push({ t: isect.tj, point: isect.point, otherEdge: isect.i, otherT: isect.ti });
  }
  
  // Sort intersections along each edge by parameter t
  for (let i = 0; i < n; i++) {
    edgeIntersections[i].sort((a, b) => a.t - b.t);
  }
  
  // Build node list: original vertices + intersection points
  const nodes = [];
  const nodeMap = new Map(); // key -> node index
  
  // Add original vertices
  for (let i = 0; i < n; i++) {
    const key = `v${i}`;
    nodeMap.set(key, nodes.length);
    nodes.push({ x: points[i].x, y: points[i].y, key: key, edges: [] });
  }
  
  // Add intersection points
  let isectIdx = 0;
  for (const isect of intersections) {
    const key = `i${isectIdx}`;
    nodeMap.set(key, nodes.length);
    nodes.push({ x: isect.point.x, y: isect.point.y, key: key, edges: [], isIntersection: true });
    isectIdx++;
  }
  
  // Build edges in the graph
  // For each original edge, add segments between vertices and intersection points
  for (let i = 0; i < n; i++) {
    const startKey = `v${i}`;
    const endKey = `v${(i + 1) % n}`;
    
    const isects = edgeIntersections[i];
    
    if (isects.length === 0) {
      // No intersections on this edge - connect start to end
      const startIdx = nodeMap.get(startKey);
      const endIdx = nodeMap.get(endKey);
      nodes[startIdx].edges.push(endIdx);
      nodes[endIdx].edges.push(startIdx);
    } else {
      // Has intersections - connect start -> isects -> end
      let prevKey = startKey;
      for (let k = 0; k < isects.length; k++) {
        // Find the intersection node
        const isectNode = intersections.find(is => 
          is.i === i && Math.abs(is.ti - isects[k].t) < 0.0001 ||
          is.j === i && Math.abs(is.tj - isects[k].t) < 0.0001
        );
        const isectIdx = intersections.indexOf(isectNode);
        const isectKey = `i${isectIdx}`;
        
        const prevIdx = nodeMap.get(prevKey);
        const currIdx = nodeMap.get(isectKey);
        nodes[prevIdx].edges.push(currIdx);
        nodes[currIdx].edges.push(prevIdx);
        prevKey = isectKey;
      }
      // Connect last intersection to end vertex
      const prevIdx = nodeMap.get(prevKey);
      const endIdx = nodeMap.get(endKey);
      nodes[prevIdx].edges.push(endIdx);
      nodes[endIdx].edges.push(prevIdx);
    }
  }
  
  // Trace closed contours using the graph
  const contours = [];
  const usedEdges = new Set();
  
  const makeEdgeKey = (a, b) => a < b ? `${a}-${b}` : `${b}-${a}`;
  
  // Start from each intersection point and trace contours
  for (let startIdx = 0; startIdx < nodes.length; startIdx++) {
    const startNode = nodes[startIdx];
    
    for (const nextIdx of startNode.edges) {
      const edgeKey = makeEdgeKey(startIdx, nextIdx);
      if (usedEdges.has(edgeKey)) continue;
      
      // Trace a contour
      const contour = [];
      let currIdx = startIdx;
      let prevIdx = -1;
      let nextNodeIdx = nextIdx;
      let safety = 0;
      
      while (safety < 10000) {
        safety++;
        contour.push({ x: nodes[currIdx].x, y: nodes[currIdx].y });
        
        const currEdgeKey = makeEdgeKey(currIdx, nextNodeIdx);
        usedEdges.add(currEdgeKey);
        
        prevIdx = currIdx;
        currIdx = nextNodeIdx;
        
        // Find next edge (not the one we came from)
        const currNode = nodes[currIdx];
        let foundNext = false;
        
        // At intersection points, we need to turn (cross to the other edge)
        if (currNode.isIntersection) {
          // Find the edge that continues in the "right" direction
          // Use cross product to determine turning direction
          const prev = nodes[prevIdx];
          const curr = nodes[currIdx];
          
          let bestNext = -1;
          let bestAngle = Infinity;
          
          for (const candidate of currNode.edges) {
            if (candidate === prevIdx) continue;
            const candEdgeKey = makeEdgeKey(currIdx, candidate);
            if (usedEdges.has(candEdgeKey)) continue;
            
            const next = nodes[candidate];
            // Calculate angle to determine which way to turn
            const angle = Math.atan2(next.y - curr.y, next.x - curr.x) - 
                         Math.atan2(curr.y - prev.y, curr.x - prev.x);
            const normalizedAngle = ((angle + 3 * Math.PI) % (2 * Math.PI)) - Math.PI;
            
            // Prefer right turns (for clockwise traversal)
            if (normalizedAngle < bestAngle) {
              bestAngle = normalizedAngle;
              bestNext = candidate;
            }
          }
          
          if (bestNext >= 0) {
            nextNodeIdx = bestNext;
            foundNext = true;
          }
        } else {
          // Regular vertex - just follow the polygon
          for (const candidate of currNode.edges) {
            if (candidate === prevIdx) continue;
            const candEdgeKey = makeEdgeKey(currIdx, candidate);
            if (usedEdges.has(candEdgeKey)) continue;
            nextNodeIdx = candidate;
            foundNext = true;
            break;
          }
        }
        
        if (!foundNext || currIdx === startIdx) {
          break;
        }
      }
      
      // Only add contours with at least 3 points
      if (contour.length >= 3) {
        contours.push(contour);
      }
    }
  }
  
  return contours.length > 0 ? contours : [points];
}

// Find intersection point of two line segments
function lineIntersection(a1, a2, b1, b2) {
  const d1x = a2.x - a1.x;
  const d1y = a2.y - a1.y;
  const d2x = b2.x - b1.x;
  const d2y = b2.y - b1.y;
  
  const cross = d1x * d2y - d1y * d2x;
  if (Math.abs(cross) < 0.0001) return null; // Parallel
  
  const dx = b1.x - a1.x;
  const dy = b1.y - a1.y;
  
  const t1 = (dx * d2y - dy * d2x) / cross;
  const t2 = (dx * d1y - dy * d1x) / cross;
  
  // Check if intersection is within both segments (not at endpoints)
  const eps = 0.001;
  if (t1 > eps && t1 < 1 - eps && t2 > eps && t2 < 1 - eps) {
    return {
      point: {
        x: a1.x + t1 * d1x,
        y: a1.y + t1 * d1y
      },
      t1: t1,
      t2: t2
    };
  }
  
  return null;
}

// Split compound paths into separate subpath strings
// Handles two patterns:
// 1. Multiple M commands after Z (standard compound paths)
// 2. "Bridge" lines - paths where inner/outer contours are connected by L commands
//    Pattern: M A ... L B ... (inner) ... L A Z -> split into outer and inner paths
function splitCompoundPath(d) {
  if (!d || !d.trim()) return [];
  
  const commands = d.match(/([MLHVZCSQTAmlhvzcsqta])[^MLHVZCSQTAmlhvzcsqta]*/g) || [];
  if (commands.length === 0) return [];
  
  // First, try standard splitting (multiple M commands after Z, or multiple M commands in general)
  const standardSubpaths = [];
  let currentSubpath = '';
  let afterClose = false;
  let hasDrawCommands = false; // Track if current subpath has actual draw commands

  for (const cmd of commands) {
    const cmdChar = cmd[0];

    if (cmdChar === 'M' || cmdChar === 'm') {
      // Split on M after Z (standard compound path)
      // Also split on M when current subpath already has draw commands (M without Z)
      if ((afterClose || hasDrawCommands) && currentSubpath.trim()) {
        standardSubpaths.push(currentSubpath.trim());
        currentSubpath = cmd;
        afterClose = false;
        hasDrawCommands = false;
      } else {
        currentSubpath += cmd;
      }
    } else {
      currentSubpath += cmd;
      if (cmdChar === 'Z' || cmdChar === 'z') {
        afterClose = true;
        hasDrawCommands = false;
      } else {
        afterClose = false;
        // Any non-M, non-Z command is a draw command
        hasDrawCommands = true;
      }
    }
  }

  if (currentSubpath.trim()) {
    standardSubpaths.push(currentSubpath.trim());
  }

  // If we found multiple subpaths via standard method, use that
  if (standardSubpaths.length > 1) {
    return standardSubpaths;
  }
  
  // Otherwise, check for bridge line patterns
  // These are single paths that connect inner/outer contours with L commands
  const parseNums = (str) => (str.match(/[-+]?[0-9]*\.?[0-9]+(?:[eE][-+]?[0-9]+)?/g) || []).map(Number);
  
  let currentX = 0, currentY = 0;
  let startX = 0, startY = 0;
  
  // Build list of command positions
  const cmdPositions = [];
  
  for (let i = 0; i < commands.length; i++) {
    const cmdStr = commands[i];
    const cmd = cmdStr[0];
    const nums = parseNums(cmdStr.slice(1));
    
    const posEntry = { 
      cmd, 
      cmdStr, 
      index: i,
      startX: currentX, 
      startY: currentY,
      endX: currentX,
      endY: currentY,
      subpathStartX: startX,
      subpathStartY: startY
    };
    
    switch (cmd) {
      case 'M':
        if (nums.length >= 2) {
          currentX = nums[nums.length - 2];
          currentY = nums[nums.length - 1];
          startX = nums[0];
          startY = nums[1];
          posEntry.subpathStartX = startX;
          posEntry.subpathStartY = startY;
        }
        break;
      case 'm':
        if (nums.length >= 2) {
          currentX += nums[0];
          currentY += nums[1];
          startX = currentX;
          startY = currentY;
          posEntry.subpathStartX = startX;
          posEntry.subpathStartY = startY;
        }
        break;
      case 'L':
        if (nums.length >= 2) {
          currentX = nums[nums.length - 2];
          currentY = nums[nums.length - 1];
        }
        break;
      case 'l':
        if (nums.length >= 2) {
          currentX += nums[nums.length - 2];
          currentY += nums[nums.length - 1];
        }
        break;
      case 'H':
        if (nums.length >= 1) currentX = nums[nums.length - 1];
        break;
      case 'h':
        if (nums.length >= 1) currentX += nums[nums.length - 1];
        break;
      case 'V':
        if (nums.length >= 1) currentY = nums[nums.length - 1];
        break;
      case 'v':
        if (nums.length >= 1) currentY += nums[nums.length - 1];
        break;
      case 'C':
        if (nums.length >= 6) {
          currentX = nums[nums.length - 2];
          currentY = nums[nums.length - 1];
        }
        break;
      case 'c':
        if (nums.length >= 6) {
          currentX += nums[nums.length - 2];
          currentY += nums[nums.length - 1];
        }
        break;
      case 'S':
      case 'Q':
        if (nums.length >= 4) {
          currentX = nums[nums.length - 2];
          currentY = nums[nums.length - 1];
        }
        break;
      case 's':
      case 'q':
        if (nums.length >= 4) {
          currentX += nums[nums.length - 2];
          currentY += nums[nums.length - 1];
        }
        break;
      case 'T':
        if (nums.length >= 2) {
          currentX = nums[nums.length - 2];
          currentY = nums[nums.length - 1];
        }
        break;
      case 't':
        if (nums.length >= 2) {
          currentX += nums[nums.length - 2];
          currentY += nums[nums.length - 1];
        }
        break;
      case 'A':
        if (nums.length >= 7) {
          currentX = nums[nums.length - 2];
          currentY = nums[nums.length - 1];
        }
        break;
      case 'a':
        if (nums.length >= 7) {
          currentX += nums[nums.length - 2];
          currentY += nums[nums.length - 1];
        }
        break;
      case 'Z':
      case 'z':
        currentX = startX;
        currentY = startY;
        break;
    }
    
    posEntry.endX = currentX;
    posEntry.endY = currentY;
    cmdPositions.push(posEntry);
  }
  
  // Look for bridge patterns: L command that returns to subpath start point
  // NOTE: Skip L commands that are followed by Z - those are normal closing lines, not bridges
  const threshold = 0.5;
  const bridgeIndices = [];
  
  for (let i = 1; i < cmdPositions.length - 1; i++) {
    const pos = cmdPositions[i];
    const nextPos = cmdPositions[i + 1];
    
    // Skip if this L is followed by Z (it's a closing line, not a bridge)
    if (nextPos && (nextPos.cmd === 'Z' || nextPos.cmd === 'z')) {
      continue;
    }
    
    if ((pos.cmd === 'L' || pos.cmd === 'l') && 
        Math.abs(pos.endX - pos.subpathStartX) < threshold &&
        Math.abs(pos.endY - pos.subpathStartY) < threshold) {
      bridgeIndices.push(i);
    }
  }
  
  // If we found a bridge back to start
  if (bridgeIndices.length === 1) {
    const bridgeIdx = bridgeIndices[0];
    
    // Find the outgoing bridge (L that started the inner section)
    let outgoingIdx = -1;
    for (let i = bridgeIdx - 1; i >= 0; i--) {
      const pos = cmdPositions[i];
      if (pos.cmd === 'L' || pos.cmd === 'l') {
        const prevPos = cmdPositions[i - 1];
        if (prevPos) {
          const jumpDist = Math.sqrt(
            Math.pow(pos.endX - prevPos.endX, 2) +
            Math.pow(pos.endY - prevPos.endY, 2)
          );
          if (jumpDist > 5) {
            outgoingIdx = i;
            break;
          }
        }
      }
    }
    
    if (outgoingIdx >= 0) {
      const outerPath = commands.slice(0, outgoingIdx).join('') + 'Z';
      const innerStartPos = cmdPositions[outgoingIdx];
      const innerPath = `M${innerStartPos.endX},${innerStartPos.endY}` + 
                        commands.slice(outgoingIdx + 1, bridgeIdx).join('') + 'Z';
      
      const paths = [outerPath, innerPath].filter(p => p.length > 5);
      if (paths.length > 1) return paths;
    }
  }
  
  // Check for two-bridge pattern (L to point, inner, L back from point)
  // This detects paths where outer and inner contours are connected by bridge lines
  // NOTE: Skip consecutive L commands - those are normal line sequences, not bridges
  if (bridgeIndices.length === 0) {
    const lCommands = cmdPositions.filter(p => p.cmd === 'L' || p.cmd === 'l');
    for (let i = 0; i < lCommands.length; i++) {
      for (let j = i + 1; j < lCommands.length; j++) {
        // Skip if these are consecutive commands (normal line sequence, not bridge)
        if (lCommands[j].index === lCommands[i].index + 1) {
          continue;
        }
        
        const dist = Math.sqrt(
          Math.pow(lCommands[i].endX - lCommands[j].startX, 2) +
          Math.pow(lCommands[i].endY - lCommands[j].startY, 2)
        );
        if (dist < threshold) {
          const idx1 = lCommands[i].index;
          const idx2 = lCommands[j].index;
          
          const outerPath = commands.slice(0, idx1).join('') + 
                            commands.slice(idx2 + 1).join('');
          const innerStartPos = cmdPositions[idx1];
          const innerPath = `M${innerStartPos.endX},${innerStartPos.endY}` +
                            commands.slice(idx1 + 1, idx2).join('') + 'Z';
          
          const paths = [outerPath, innerPath].filter(p => p.length > 5);
          if (paths.length > 1) return paths;
        }
      }
    }
  }
  
  // No splitting needed - return single path
  return standardSubpaths.length > 0 ? standardSubpaths : [d];
}

// Check if a shape is truly open (first and last points are far apart)
// DISABLED: Since we always output closed="1" in Resolume XML, all shapes render as closed.
// This check was causing false positives for shapes with Z commands where the path
// naturally doesn't end at the start point (Resolume handles the closing edge automatically).
function isShapeOpen(points, bbox, sourceType) {
  // Always return false - Resolume's closed="1" handles all closing
  return false;
}

// Check if polygon edges self-intersect (causes rendering issues in Resolume)
// This includes checking if the "closing edge" (from last to first point) intersects other edges
function hasSelfIntersection(points, sourceType, isCompoundSubpath = false) {
  if (!points || points.length < 3) return false;
  
  // Skip compound subpaths - these are often valid shapes that work with fill rules
  // and may appear self-intersecting when analyzed individually
  if (isCompoundSubpath) return false;
  
  // Skip complex paths (many points) - these are typically from professional design software
  // and use fill rules (evenodd/nonzero) to create holes. Self-intersection is intentional.
  // Threshold: paths with more than 100 points are considered complex
  if (points.length > 100) return false;
  
  // Only check polylines and paths - other shapes are generated correctly by the converter
  if (sourceType !== 'polyline' && sourceType !== 'path') return false;
  
  const n = points.length;
  
  // Check all edges including the closing edge (from last point back to first)
  for (let i = 0; i < n; i++) {
    const a1 = points[i];
    const a2 = points[(i + 1) % n];
    
    // Skip very short edges (degenerate)
    const len1 = Math.sqrt(Math.pow(a2.x - a1.x, 2) + Math.pow(a2.y - a1.y, 2));
    if (len1 < 0.5) continue;
    
    for (let j = i + 2; j < n; j++) {
      // Skip if the two edges share a vertex (adjacent edges)
      if (i === 0 && j === n - 1) continue;
      
      const b1 = points[j];
      const b2 = points[(j + 1) % n];
      
      // Skip very short edges
      const len2 = Math.sqrt(Math.pow(b2.x - b1.x, 2) + Math.pow(b2.y - b1.y, 2));
      if (len2 < 0.5) continue;
      
      if (segmentsIntersect(a1, a2, b1, b2)) {
        return true;
      }
    }
  }
  return false;
}

// Check if two line segments properly intersect (cross through each other, not just touch)
function segmentsIntersect(a1, a2, b1, b2) {
  const d1 = crossProduct(b1, b2, a1);
  const d2 = crossProduct(b1, b2, a2);
  const d3 = crossProduct(a1, a2, b1);
  const d4 = crossProduct(a1, a2, b2);
  
  // Check for proper intersection (segments cross each other)
  // Use a small epsilon to avoid floating point issues
  const eps = 0.0001;
  if (((d1 > eps && d2 < -eps) || (d1 < -eps && d2 > eps)) &&
      ((d3 > eps && d4 < -eps) || (d3 < -eps && d4 > eps))) {
    return true;
  }
  
  return false;
}

function crossProduct(o, a, b) {
  return (a.x - o.x) * (b.y - o.y) - (a.y - o.y) * (b.x - o.x);
}

// Bezier curve evaluation
function cubicBezier(t, p0, p1, p2, p3) {
  const t2 = t * t;
  const t3 = t2 * t;
  const mt = 1 - t;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;
  return {
    x: mt3 * p0.x + 3 * mt2 * t * p1.x + 3 * mt * t2 * p2.x + t3 * p3.x,
    y: mt3 * p0.y + 3 * mt2 * t * p1.y + 3 * mt * t2 * p2.y + t3 * p3.y
  };
}

function quadraticBezier(t, p0, p1, p2) {
  const mt = 1 - t;
  const mt2 = mt * mt;
  const t2 = t * t;
  return {
    x: mt2 * p0.x + 2 * mt * t * p1.x + t2 * p2.x,
    y: mt2 * p0.y + 2 * mt * t * p1.y + t2 * p2.y
  };
}

// Rasterize a cubic bezier curve into line segments
function rasterizeCubicBezier(p0, p1, p2, p3, resolution) {
  // Calculate approximate curve length using control polygon
  const d01 = Math.sqrt(Math.pow(p1.x - p0.x, 2) + Math.pow(p1.y - p0.y, 2));
  const d12 = Math.sqrt(Math.pow(p2.x - p1.x, 2) + Math.pow(p2.y - p1.y, 2));
  const d23 = Math.sqrt(Math.pow(p3.x - p2.x, 2) + Math.pow(p3.y - p2.y, 2));
  const approxLength = d01 + d12 + d23;
  
  // Use adaptive resolution: ensure minimum edge length of 2 pixels
  // but cap at the requested resolution
  const minEdgeLength = 2;
  const adaptiveRes = Math.max(1, Math.min(resolution, Math.ceil(approxLength / minEdgeLength)));
  
  const points = [];
  for (let i = 1; i <= adaptiveRes; i++) {
    const t = i / adaptiveRes;
    points.push(cubicBezier(t, p0, p1, p2, p3));
  }
  return points;
}

// Rasterize a quadratic bezier curve into line segments
function rasterizeQuadraticBezier(p0, p1, p2, resolution) {
  // Calculate approximate curve length using control polygon
  const d01 = Math.sqrt(Math.pow(p1.x - p0.x, 2) + Math.pow(p1.y - p0.y, 2));
  const d12 = Math.sqrt(Math.pow(p2.x - p1.x, 2) + Math.pow(p2.y - p1.y, 2));
  const approxLength = d01 + d12;
  
  // Use adaptive resolution: ensure minimum edge length of 2 pixels
  const minEdgeLength = 2;
  const adaptiveRes = Math.max(1, Math.min(resolution, Math.ceil(approxLength / minEdgeLength)));
  
  const points = [];
  for (let i = 1; i <= adaptiveRes; i++) {
    const t = i / adaptiveRes;
    points.push(quadraticBezier(t, p0, p1, p2));
  }
  return points;
}

// Parse SVG path preserving bezier control points (for mask bezier mode)
// Resolume format: anchor, cp_out, cp_in, anchor, cp_out, cp_in, ...
// segments: one 'C' per cubic bezier curve, one 'L' per linear segment
function parseSvgPathWithBezier(d) {
  const points = [];      // All points in Resolume order
  let segments = '';      // Segment types: L=linear, C=cubic bezier
  
  const commands = d.match(/([MLHVZCSQTAmlhvzcsqta])[^MLHVZCSQTAmlhvzcsqta]*/g) || [];
  
  let currentX = 0, currentY = 0;
  let startX = 0, startY = 0;
  let lastControlX = 0, lastControlY = 0;
  let lastCommand = '';
  let firstPoint = true;
  
  for (const cmdStr of commands) {
    const cmd = cmdStr[0];
    const coordStr = cmdStr.slice(1).trim();
    
    // Use special parsing for arc commands (handles concatenated flag digits)
    const nums = (cmd === 'A' || cmd === 'a') 
      ? parseArcParams(coordStr)
      : (coordStr.match(/[-+]?[0-9]*\.?[0-9]+(?:[eE][-+]?[0-9]+)?/g) || []).map(Number);
    
    switch (cmd) {
      case 'M':
      case 'm': {
        const isRelative = cmd === 'm';
        for (let i = 0; i < nums.length; i += 2) {
          if (isRelative && !firstPoint) {
            currentX += nums[i];
            currentY += nums[i + 1];
          } else {
            currentX = nums[i];
            currentY = nums[i + 1];
          }
          if (i === 0) { 
            startX = currentX; 
            startY = currentY; 
          }
          // Add anchor point
          points.push({ x: currentX, y: currentY });
          if (!firstPoint) {
            segments += 'L'; // Implicit lineto after first M point
          }
          firstPoint = false;
        }
        break;
      }
      case 'L':
      case 'l': {
        const isRelative = cmd === 'l';
        for (let i = 0; i < nums.length; i += 2) {
          if (isRelative) {
            currentX += nums[i];
            currentY += nums[i + 1];
          } else {
            currentX = nums[i];
            currentY = nums[i + 1];
          }
          points.push({ x: currentX, y: currentY });
          segments += 'L';
        }
        break;
      }
      case 'H':
      case 'h': {
        const isRelative = cmd === 'h';
        for (const val of nums) {
          currentX = isRelative ? currentX + val : val;
          points.push({ x: currentX, y: currentY });
          segments += 'L';
        }
        break;
      }
      case 'V':
      case 'v': {
        const isRelative = cmd === 'v';
        for (const val of nums) {
          currentY = isRelative ? currentY + val : val;
          points.push({ x: currentX, y: currentY });
          segments += 'L';
        }
        break;
      }
      case 'C':
      case 'c': {
        const isRelative = cmd === 'c';
        for (let i = 0; i < nums.length; i += 6) {
          // Control point 1 (out handle from current anchor)
          const cp1x = isRelative ? currentX + nums[i] : nums[i];
          const cp1y = isRelative ? currentY + nums[i + 1] : nums[i + 1];
          // Control point 2 (in handle to next anchor)
          const cp2x = isRelative ? currentX + nums[i + 2] : nums[i + 2];
          const cp2y = isRelative ? currentY + nums[i + 3] : nums[i + 3];
          // End anchor
          const endX = isRelative ? currentX + nums[i + 4] : nums[i + 4];
          const endY = isRelative ? currentY + nums[i + 5] : nums[i + 5];
          
          // Resolume order: cp1, cp2, end_anchor
          points.push({ x: cp1x, y: cp1y });
          points.push({ x: cp2x, y: cp2y });
          points.push({ x: endX, y: endY });
          segments += 'C';
          
          lastControlX = cp2x;
          lastControlY = cp2y;
          currentX = endX;
          currentY = endY;
        }
        break;
      }
      case 'S':
      case 's': {
        const isRelative = cmd === 's';
        for (let i = 0; i < nums.length; i += 4) {
          // Reflect last control point for cp1
          let cp1x = currentX, cp1y = currentY;
          if (lastCommand === 'C' || lastCommand === 'c' || lastCommand === 'S' || lastCommand === 's') {
            cp1x = 2 * currentX - lastControlX;
            cp1y = 2 * currentY - lastControlY;
          }
          
          const cp2x = isRelative ? currentX + nums[i] : nums[i];
          const cp2y = isRelative ? currentY + nums[i + 1] : nums[i + 1];
          const endX = isRelative ? currentX + nums[i + 2] : nums[i + 2];
          const endY = isRelative ? currentY + nums[i + 3] : nums[i + 3];
          
          points.push({ x: cp1x, y: cp1y });
          points.push({ x: cp2x, y: cp2y });
          points.push({ x: endX, y: endY });
          segments += 'C';
          
          lastControlX = cp2x;
          lastControlY = cp2y;
          currentX = endX;
          currentY = endY;
        }
        break;
      }
      case 'Q':
      case 'q': {
        // Quadratic bezier - convert to cubic
        const isRelative = cmd === 'q';
        for (let i = 0; i < nums.length; i += 4) {
          const cpx = isRelative ? currentX + nums[i] : nums[i];
          const cpy = isRelative ? currentY + nums[i + 1] : nums[i + 1];
          const endX = isRelative ? currentX + nums[i + 2] : nums[i + 2];
          const endY = isRelative ? currentY + nums[i + 3] : nums[i + 3];
          
          // Convert quadratic to cubic control points
          const cp1x = currentX + (2/3) * (cpx - currentX);
          const cp1y = currentY + (2/3) * (cpy - currentY);
          const cp2x = endX + (2/3) * (cpx - endX);
          const cp2y = endY + (2/3) * (cpy - endY);
          
          points.push({ x: cp1x, y: cp1y });
          points.push({ x: cp2x, y: cp2y });
          points.push({ x: endX, y: endY });
          segments += 'C';
          
          lastControlX = cpx;
          lastControlY = cpy;
          currentX = endX;
          currentY = endY;
        }
        break;
      }
      case 'T':
      case 't': {
        const isRelative = cmd === 't';
        for (let i = 0; i < nums.length; i += 2) {
          let cpx = currentX, cpy = currentY;
          if (lastCommand === 'Q' || lastCommand === 'q' || lastCommand === 'T' || lastCommand === 't') {
            cpx = 2 * currentX - lastControlX;
            cpy = 2 * currentY - lastControlY;
          }
          
          const endX = isRelative ? currentX + nums[i] : nums[i];
          const endY = isRelative ? currentY + nums[i + 1] : nums[i + 1];
          
          const cp1x = currentX + (2/3) * (cpx - currentX);
          const cp1y = currentY + (2/3) * (cpy - currentY);
          const cp2x = endX + (2/3) * (cpx - endX);
          const cp2y = endY + (2/3) * (cpy - endY);
          
          points.push({ x: cp1x, y: cp1y });
          points.push({ x: cp2x, y: cp2y });
          points.push({ x: endX, y: endY });
          segments += 'C';
          
          lastControlX = cpx;
          lastControlY = cpy;
          currentX = endX;
          currentY = endY;
        }
        break;
      }
      case 'A':
      case 'a': {
        // Arc - convert to line segments (bezier arc approximation is complex)
        const isRelative = cmd === 'a';
        for (let i = 0; i < nums.length; i += 7) {
          const endX = isRelative ? currentX + nums[i + 5] : nums[i + 5];
          const endY = isRelative ? currentY + nums[i + 6] : nums[i + 6];
          points.push({ x: endX, y: endY });
          segments += 'L';
          currentX = endX;
          currentY = endY;
        }
        break;
      }
      case 'Z':
      case 'z':
        // Don't add closing point - Resolume (closed="1") handles closing automatically
        currentX = startX;
        currentY = startY;
        break;
    }
    lastCommand = cmd;
  }
  
  return {
    points,
    segments,
    hasBezier: segments.includes('C')
  };
}

// Approximate arc with line segments
function rasterizeArc(current, rx, ry, xAxisRotation, largeArcFlag, sweepFlag, endX, endY, resolution) {
  // Handle degenerate cases
  if (rx === 0 || ry === 0 || (current.x === endX && current.y === endY)) {
    return [{ x: endX, y: endY }];
  }
  
  rx = Math.abs(rx);
  ry = Math.abs(ry);
  
  const phi = (xAxisRotation * Math.PI) / 180;
  const cosPhi = Math.cos(phi);
  const sinPhi = Math.sin(phi);
  
  // Step 1: Compute (x1', y1')
  const dx = (current.x - endX) / 2;
  const dy = (current.y - endY) / 2;
  const x1p = cosPhi * dx + sinPhi * dy;
  const y1p = -sinPhi * dx + cosPhi * dy;
  
  // Step 2: Compute (cx', cy')
  let rxSq = rx * rx;
  let rySq = ry * ry;
  const x1pSq = x1p * x1p;
  const y1pSq = y1p * y1p;
  
  // Correct radii if necessary
  const lambda = x1pSq / rxSq + y1pSq / rySq;
  if (lambda > 1) {
    const sqrtLambda = Math.sqrt(lambda);
    rx *= sqrtLambda;
    ry *= sqrtLambda;
    rxSq = rx * rx;
    rySq = ry * ry;
  }
  
  let sq = Math.max(0, (rxSq * rySq - rxSq * y1pSq - rySq * x1pSq) / (rxSq * y1pSq + rySq * x1pSq));
  sq = Math.sqrt(sq);
  if (largeArcFlag === sweepFlag) sq = -sq;
  
  const cxp = sq * (rx * y1p / ry);
  const cyp = sq * -(ry * x1p / rx);
  
  // Step 3: Compute (cx, cy)
  const cx = cosPhi * cxp - sinPhi * cyp + (current.x + endX) / 2;
  const cy = sinPhi * cxp + cosPhi * cyp + (current.y + endY) / 2;
  
  // Step 4: Compute theta1 and dtheta
  const ux = (x1p - cxp) / rx;
  const uy = (y1p - cyp) / ry;
  const vx = (-x1p - cxp) / rx;
  const vy = (-y1p - cyp) / ry;
  
  const n = Math.sqrt(ux * ux + uy * uy);
  let p = ux;
  let theta1 = Math.acos(Math.max(-1, Math.min(1, p / n)));
  if (uy < 0) theta1 = -theta1;
  
  const nn = Math.sqrt((ux * ux + uy * uy) * (vx * vx + vy * vy));
  p = ux * vx + uy * vy;
  let dtheta = Math.acos(Math.max(-1, Math.min(1, p / nn)));
  if (ux * vy - uy * vx < 0) dtheta = -dtheta;
  
  if (sweepFlag && dtheta < 0) dtheta += 2 * Math.PI;
  if (!sweepFlag && dtheta > 0) dtheta -= 2 * Math.PI;
  
  // Generate points
  const points = [];
  const steps = Math.max(Math.ceil(Math.abs(dtheta) / (Math.PI / resolution)), 1);
  
  for (let i = 1; i <= steps; i++) {
    const t = i / steps;
    const theta = theta1 + t * dtheta;
    const cosTheta = Math.cos(theta);
    const sinTheta = Math.sin(theta);
    
    const x = cosPhi * rx * cosTheta - sinPhi * ry * sinTheta + cx;
    const y = sinPhi * rx * cosTheta + cosPhi * ry * sinTheta + cy;
    
    points.push({ x, y });
  }
  
  return points;
}

// SVG Path Parser with bezier rasterization
function parseSvgPath(d, bezierResolution = 3) {
  const points = [];
  const commands = d.match(/([MLHVZCSQTAmlhvzcsqta])[^MLHVZCSQTAmlhvzcsqta]*/g) || [];
  
  let currentX = 0, currentY = 0;
  let startX = 0, startY = 0;
  let lastControlX = 0, lastControlY = 0;
  let lastCommand = '';
  
  for (const cmdStr of commands) {
    const cmd = cmdStr[0];
    const coordStr = cmdStr.slice(1).trim();
    
    // Use special parsing for arc commands (handles concatenated flag digits)
    const nums = (cmd === 'A' || cmd === 'a') 
      ? parseArcParams(coordStr)
      : (coordStr.match(/[-+]?[0-9]*\.?[0-9]+(?:[eE][-+]?[0-9]+)?/g) || []).map(Number);
    
    switch (cmd) {
      case 'M':
        for (let i = 0; i < nums.length; i += 2) {
          currentX = nums[i];
          currentY = nums[i + 1];
          if (i === 0) { startX = currentX; startY = currentY; }
          points.push({ x: currentX, y: currentY });
        }
        break;
      case 'm':
        for (let i = 0; i < nums.length; i += 2) {
          currentX += nums[i];
          currentY += nums[i + 1];
          if (i === 0) { startX = currentX; startY = currentY; }
          points.push({ x: currentX, y: currentY });
        }
        break;
      case 'L':
        for (let i = 0; i < nums.length; i += 2) {
          currentX = nums[i];
          currentY = nums[i + 1];
          points.push({ x: currentX, y: currentY });
        }
        break;
      case 'l':
        for (let i = 0; i < nums.length; i += 2) {
          currentX += nums[i];
          currentY += nums[i + 1];
          points.push({ x: currentX, y: currentY });
        }
        break;
      case 'H':
        for (const x of nums) {
          currentX = x;
          points.push({ x: currentX, y: currentY });
        }
        break;
      case 'h':
        for (const dx of nums) {
          currentX += dx;
          points.push({ x: currentX, y: currentY });
        }
        break;
      case 'V':
        for (const y of nums) {
          currentY = y;
          points.push({ x: currentX, y: currentY });
        }
        break;
      case 'v':
        for (const dy of nums) {
          currentY += dy;
          points.push({ x: currentX, y: currentY });
        }
        break;
      case 'C': // Cubic bezier (absolute)
        for (let i = 0; i < nums.length; i += 6) {
          const p0 = { x: currentX, y: currentY };
          const p1 = { x: nums[i], y: nums[i + 1] };
          const p2 = { x: nums[i + 2], y: nums[i + 3] };
          const p3 = { x: nums[i + 4], y: nums[i + 5] };
          const rasterized = rasterizeCubicBezier(p0, p1, p2, p3, bezierResolution);
          points.push(...rasterized);
          currentX = p3.x;
          currentY = p3.y;
          lastControlX = p2.x;
          lastControlY = p2.y;
        }
        break;
      case 'c': // Cubic bezier (relative)
        for (let i = 0; i < nums.length; i += 6) {
          const p0 = { x: currentX, y: currentY };
          const p1 = { x: currentX + nums[i], y: currentY + nums[i + 1] };
          const p2 = { x: currentX + nums[i + 2], y: currentY + nums[i + 3] };
          const p3 = { x: currentX + nums[i + 4], y: currentY + nums[i + 5] };
          const rasterized = rasterizeCubicBezier(p0, p1, p2, p3, bezierResolution);
          points.push(...rasterized);
          lastControlX = p2.x;
          lastControlY = p2.y;
          currentX = p3.x;
          currentY = p3.y;
        }
        break;
      case 'S': // Smooth cubic bezier (absolute)
        for (let i = 0; i < nums.length; i += 4) {
          const p0 = { x: currentX, y: currentY };
          // Per SVG spec: reflect last control point only if previous command was C/c/S/s
          let cp1x = currentX, cp1y = currentY;
          if (lastCommand === 'C' || lastCommand === 'c' || lastCommand === 'S' || lastCommand === 's') {
            cp1x = 2 * currentX - lastControlX;
            cp1y = 2 * currentY - lastControlY;
          }
          const p1 = { x: cp1x, y: cp1y };
          const p2 = { x: nums[i], y: nums[i + 1] };
          const p3 = { x: nums[i + 2], y: nums[i + 3] };
          const rasterized = rasterizeCubicBezier(p0, p1, p2, p3, bezierResolution);
          points.push(...rasterized);
          lastControlX = p2.x;
          lastControlY = p2.y;
          currentX = p3.x;
          currentY = p3.y;
        }
        break;
      case 's': // Smooth cubic bezier (relative)
        for (let i = 0; i < nums.length; i += 4) {
          const p0 = { x: currentX, y: currentY };
          // Per SVG spec: reflect last control point only if previous command was C/c/S/s
          let scp1x = currentX, scp1y = currentY;
          if (lastCommand === 'C' || lastCommand === 'c' || lastCommand === 'S' || lastCommand === 's') {
            scp1x = 2 * currentX - lastControlX;
            scp1y = 2 * currentY - lastControlY;
          }
          const p1 = { x: scp1x, y: scp1y };
          const p2 = { x: currentX + nums[i], y: currentY + nums[i + 1] };
          const p3 = { x: currentX + nums[i + 2], y: currentY + nums[i + 3] };
          const rasterized = rasterizeCubicBezier(p0, p1, p2, p3, bezierResolution);
          points.push(...rasterized);
          lastControlX = p2.x;
          lastControlY = p2.y;
          currentX = p3.x;
          currentY = p3.y;
        }
        break;
      case 'Q': // Quadratic bezier (absolute)
        for (let i = 0; i < nums.length; i += 4) {
          const p0 = { x: currentX, y: currentY };
          const p1 = { x: nums[i], y: nums[i + 1] };
          const p2 = { x: nums[i + 2], y: nums[i + 3] };
          const rasterized = rasterizeQuadraticBezier(p0, p1, p2, bezierResolution);
          points.push(...rasterized);
          lastControlX = p1.x;
          lastControlY = p1.y;
          currentX = p2.x;
          currentY = p2.y;
        }
        break;
      case 'q': // Quadratic bezier (relative)
        for (let i = 0; i < nums.length; i += 4) {
          const p0 = { x: currentX, y: currentY };
          const p1 = { x: currentX + nums[i], y: currentY + nums[i + 1] };
          const p2 = { x: currentX + nums[i + 2], y: currentY + nums[i + 3] };
          const rasterized = rasterizeQuadraticBezier(p0, p1, p2, bezierResolution);
          points.push(...rasterized);
          lastControlX = p1.x;
          lastControlY = p1.y;
          currentX = p2.x;
          currentY = p2.y;
        }
        break;
      case 'T': // Smooth quadratic bezier (absolute)
        for (let i = 0; i < nums.length; i += 2) {
          const p0 = { x: currentX, y: currentY };
          // Per SVG spec: reflect last control point only if previous command was Q/q/T/t
          let tcp1x = currentX, tcp1y = currentY;
          if (lastCommand === 'Q' || lastCommand === 'q' || lastCommand === 'T' || lastCommand === 't') {
            tcp1x = 2 * currentX - lastControlX;
            tcp1y = 2 * currentY - lastControlY;
          }
          const p1 = { x: tcp1x, y: tcp1y };
          const p2 = { x: nums[i], y: nums[i + 1] };
          const rasterized = rasterizeQuadraticBezier(p0, p1, p2, bezierResolution);
          points.push(...rasterized);
          lastControlX = p1.x;
          lastControlY = p1.y;
          currentX = p2.x;
          currentY = p2.y;
        }
        break;
      case 't': // Smooth quadratic bezier (relative)
        for (let i = 0; i < nums.length; i += 2) {
          const p0 = { x: currentX, y: currentY };
          // Per SVG spec: reflect last control point only if previous command was Q/q/T/t
          let trcp1x = currentX, trcp1y = currentY;
          if (lastCommand === 'Q' || lastCommand === 'q' || lastCommand === 'T' || lastCommand === 't') {
            trcp1x = 2 * currentX - lastControlX;
            trcp1y = 2 * currentY - lastControlY;
          }
          const p1 = { x: trcp1x, y: trcp1y };
          const p2 = { x: currentX + nums[i], y: currentY + nums[i + 1] };
          const rasterized = rasterizeQuadraticBezier(p0, p1, p2, bezierResolution);
          points.push(...rasterized);
          lastControlX = p1.x;
          lastControlY = p1.y;
          currentX = p2.x;
          currentY = p2.y;
        }
        break;
      case 'A': // Arc (absolute)
        for (let i = 0; i < nums.length; i += 7) {
          const rasterized = rasterizeArc(
            { x: currentX, y: currentY },
            nums[i], nums[i + 1], nums[i + 2],
            nums[i + 3], nums[i + 4],
            nums[i + 5], nums[i + 6],
            bezierResolution
          );
          points.push(...rasterized);
          currentX = nums[i + 5];
          currentY = nums[i + 6];
        }
        break;
      case 'a': // Arc (relative)
        for (let i = 0; i < nums.length; i += 7) {
          const endX = currentX + nums[i + 5];
          const endY = currentY + nums[i + 6];
          const rasterized = rasterizeArc(
            { x: currentX, y: currentY },
            nums[i], nums[i + 1], nums[i + 2],
            nums[i + 3], nums[i + 4],
            endX, endY,
            bezierResolution
          );
          points.push(...rasterized);
          currentX = endX;
          currentY = endY;
        }
        break;
      case 'Z':
      case 'z':
        // Don't add closing point - both preview (<polygon>) and Resolume (closed="1") 
        // handle closing automatically. Adding it here causes issues:
        // 1. Creates first==last which dedup removes
        // 2. This creates artificial gap that triggers false "open" warnings
        currentX = startX;
        currentY = startY;
        break;
    }
    lastCommand = cmd;
  }

  return points;
}

function parsePolygonPoints(pointsStr) {
  const coords = pointsStr.match(/[-+]?[0-9]*\.?[0-9]+(?:[eE][-+]?[0-9]+)?/g) || [];
  const nums = coords.map(Number);
  const points = [];
  for (let i = 0; i < nums.length; i += 2) {
    points.push({ x: nums[i], y: nums[i + 1] });
  }
  return points;
}

function applyTransform(points, transformStr) {
  if (!transformStr || !transformStr.trim()) return points;
  
  // Parse all transforms in the string
  const transformRegex = /(matrix|translate|scale|rotate|skewX|skewY)\s*\(\s*([^)]+)\s*\)/gi;
  const transforms = [];
  let match;
  
  while ((match = transformRegex.exec(transformStr)) !== null) {
    const type = match[1].toLowerCase();
    const values = match[2].match(/[-+]?[0-9]*\.?[0-9]+(?:[eE][-+]?[0-9]+)?/g)?.map(Number) || [];
    transforms.push({ type, values });
  }
  
  if (transforms.length === 0) return points;
  
  // Convert each transform to a matrix and combine
  let matrix = [1, 0, 0, 1, 0, 0]; // Identity matrix [a, b, c, d, e, f]
  
  for (const { type, values } of transforms) {
    let m;
    switch (type) {
      case 'matrix':
        if (values.length >= 6) {
          m = values.slice(0, 6);
        }
        break;
      case 'translate':
        const tx = values[0] || 0;
        const ty = values[1] || 0;
        m = [1, 0, 0, 1, tx, ty];
        break;
      case 'scale':
        const sx = values[0] || 1;
        const sy = values.length > 1 ? values[1] : sx;
        m = [sx, 0, 0, sy, 0, 0];
        break;
      case 'rotate':
        const angle = (values[0] || 0) * Math.PI / 180;
        const cos = Math.cos(angle);
        const sin = Math.sin(angle);
        if (values.length >= 3) {
          // rotate(angle, cx, cy)
          const cx = values[1];
          const cy = values[2];
          // Translate to origin, rotate, translate back
          m = [cos, sin, -sin, cos, cx - cos * cx + sin * cy, cy - sin * cx - cos * cy];
        } else {
          m = [cos, sin, -sin, cos, 0, 0];
        }
        break;
      case 'skewx':
        const skewXAngle = (values[0] || 0) * Math.PI / 180;
        m = [1, 0, Math.tan(skewXAngle), 1, 0, 0];
        break;
      case 'skewy':
        const skewYAngle = (values[0] || 0) * Math.PI / 180;
        m = [1, Math.tan(skewYAngle), 0, 1, 0, 0];
        break;
    }
    
    if (m) {
      // Multiply matrices: matrix = matrix * m
      const [a1, b1, c1, d1, e1, f1] = matrix;
      const [a2, b2, c2, d2, e2, f2] = m;
      matrix = [
        a1 * a2 + c1 * b2,
        b1 * a2 + d1 * b2,
        a1 * c2 + c1 * d2,
        b1 * c2 + d1 * d2,
        a1 * e2 + c1 * f2 + e1,
        b1 * e2 + d1 * f2 + f1
      ];
    }
  }
  
  // Apply combined matrix to all points
  const [a, b, c, d, e, f] = matrix;
  return points.map(p => ({
    x: a * p.x + c * p.y + e,
    y: b * p.x + d * p.y + f
  }));
}

// Extract artboard size from SVG (viewBox or width/height attributes)
function getArtboardSize(svgText) {
  const parser = new DOMParser();
  const doc = parser.parseFromString(svgText, 'image/svg+xml');
  const svg = doc.querySelector('svg');
  
  if (!svg) return null;
  
  let width = null;
  let height = null;
  
  // First try viewBox
  const viewBox = svg.getAttribute('viewBox');
  if (viewBox) {
    const parts = viewBox.split(/[\s,]+/).map(Number);
    if (parts.length >= 4 && !isNaN(parts[2]) && !isNaN(parts[3])) {
      width = parts[2];
      height = parts[3];
    }
  }
  
  // If no viewBox, try width/height attributes
  if (width === null || height === null) {
    const w = svg.getAttribute('width');
    const h = svg.getAttribute('height');
    
    // Parse width - handle units like "100px", "100", "100%"
    if (w) {
      const wMatch = w.match(/^([\d.]+)(px|pt|mm|cm|in)?$/i);
      if (wMatch) {
        let wVal = parseFloat(wMatch[1]);
        // Convert units to pixels (approximate)
        const unit = (wMatch[2] || '').toLowerCase();
        if (unit === 'pt') wVal *= 1.333;
        else if (unit === 'mm') wVal *= 3.7795;
        else if (unit === 'cm') wVal *= 37.795;
        else if (unit === 'in') wVal *= 96;
        width = Math.round(wVal);
      }
    }
    
    if (h) {
      const hMatch = h.match(/^([\d.]+)(px|pt|mm|cm|in)?$/i);
      if (hMatch) {
        let hVal = parseFloat(hMatch[1]);
        const unit = (hMatch[2] || '').toLowerCase();
        if (unit === 'pt') hVal *= 1.333;
        else if (unit === 'mm') hVal *= 3.7795;
        else if (unit === 'cm') hVal *= 37.795;
        else if (unit === 'in') hVal *= 96;
        height = Math.round(hVal);
      }
    }
  }
  
  // Return only if we have valid dimensions
  if (width && height && width > 0 && height > 0) {
    return { width: Math.round(width), height: Math.round(height) };
  }
  
  return null;
}

// Extract document title from SVG - checks multiple sources
function getDocumentTitle(svgText) {
  // Try to extract from XMP metadata: <dc:title><rdf:Alt><rdf:li>Title</rdf:li></rdf:Alt></dc:title>
  const xmpTitleMatch = svgText.match(/<dc:title[^>]*>[\s\S]*?<rdf:li[^>]*>([^<]+)<\/rdf:li>[\s\S]*?<\/dc:title>/i);
  if (xmpTitleMatch && xmpTitleMatch[1].trim()) {
    return xmpTitleMatch[1].trim();
  }
  
  // Try SVG <title> element
  const parser = new DOMParser();
  const doc = parser.parseFromString(svgText, 'image/svg+xml');
  const svg = doc.querySelector('svg');
  if (svg) {
    const titleElem = svg.querySelector(':scope > title');
    if (titleElem && titleElem.textContent.trim()) {
      return titleElem.textContent.trim();
    }
  }
  
  // Try Illustrator document title in metadata comments
  const aiTitleMatch = svgText.match(/<!--\s*(?:Document|Title):\s*([^-]+?)(?:\s*--|\s*$)/i);
  if (aiTitleMatch && aiTitleMatch[1].trim()) {
    return aiTitleMatch[1].trim();
  }
  
  return null;
}

function extractShapesFromSVG(svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin = 0, scaleToFit = true, extractClipPaths = false, shapeNameMode = { type: true, title: false }, autoCloseOpenPaths = false, skipStrokeOnly = false) {
  // Pre-process SVG to handle common issues with Adobe Illustrator exports
  let cleanedSvg = svgText;
  
  // 1. Remove DOCTYPE declarations with entity definitions (they cause parse errors)
  cleanedSvg = cleanedSvg.replace(/<!DOCTYPE[^>]*\[[^\]]*\]>/gis, '');
  cleanedSvg = cleanedSvg.replace(/<!DOCTYPE[^>]*>/gi, '');
  
  // 2. Replace undefined entity references with placeholder URLs
  cleanedSvg = cleanedSvg.replace(/&ns_([a-z_]+);/gi, 'http://ns.adobe.com/$1');
  
  // 3. Remove Adobe-specific processing instructions
  cleanedSvg = cleanedSvg.replace(/<\?adobe[^?]*\?>/gi, '');
  
  // 4. Add missing xlink namespace if xlink:href is used but xmlns:xlink is not declared
  if (/xlink:href/i.test(cleanedSvg) && !/xmlns:xlink/i.test(cleanedSvg)) {
    cleanedSvg = cleanedSvg.replace(/<svg([^>]*)>/i, '<svg$1 xmlns:xlink="http://www.w3.org/1999/xlink">');
  }
  
  // 5. Remove namespace-prefixed attributes (but preserve ones we care about like inkscape:label)
  // Keep xmlns/xlink/xml/inkscape/sodipodi so layer metadata survives
  cleanedSvg = cleanedSvg.replace(/\s+(?!xmlns)(?!xlink)(?!inkscape)(?!sodipodi)(?!xml)[a-z]+:[a-z]+=["'][^"']*["']/gi, '');
  
  const parser = new DOMParser();
  const doc = parser.parseFromString(cleanedSvg, 'image/svg+xml');
  
  // Check for parse errors
  const parseError = doc.querySelector('parsererror');
  if (parseError) {
    console.warn('SVG parse warning:', parseError.textContent);
    // Try to continue anyway - some errors are recoverable
  }
  
  const svg = doc.querySelector('svg');
  
  if (!svg) return [];
  
  // Extract SVG title for shape naming
  const titleElement = svg.querySelector(':scope > title');
  const svgTitle = titleElement ? titleElement.textContent.trim() : '';
  
  // Handle both old string format and new object format for backwards compatibility
  const useType = typeof shapeNameMode === 'object' ? shapeNameMode.type : shapeNameMode === 'type';
  const useTitle = typeof shapeNameMode === 'object' ? shapeNameMode.title : shapeNameMode === 'title';
  
  const viewBox = svg.getAttribute('viewBox');
  let vbX = 0, vbY = 0, vbWidth = 100, vbHeight = 100;
  
  if (viewBox) {
    const parts = viewBox.split(/[\s,]+/).map(Number);
    [vbX, vbY, vbWidth, vbHeight] = parts;
  } else {
    const w = svg.getAttribute('width');
    const h = svg.getAttribute('height');
    if (w) vbWidth = parseFloat(w);
    if (h) vbHeight = parseFloat(h);
  }
  
  // Calculate available canvas area after applying inner margin
  const availableWidth = canvasWidth - (innerMargin * 2);
  const availableHeight = canvasHeight - (innerMargin * 2);
  
  // First pass: collect all raw shapes (without canvas scaling)
  const rawShapes = [];
  let shapeCount = 0;
  
  // Tags that should be skipped (definition containers, non-renderable elements)
  // If extractClipPaths is true, we process clippath and mask contents
  const skipTags = new Set([
    'marker', 'pattern',
    'lineargradient', 'radialgradient', 'filter', 'fegaussianblur',
    'feoffset', 'feblend', 'fecolormatrix', 'fecomposite',
    'style', 'script', 'title', 'desc', 'metadata',
    'text', 'tspan', 'textpath', 'foreignobject',
    'image', 'a', 'line', 'stop'  // line has no area, stop is gradient stop
  ]);
  
  // Tags that should just recurse into children (container-like behavior)
  const recurseTags = new Set(['switch']);
  
  // Only skip clippath/mask containers if we're not extracting them
  if (!extractClipPaths) {
    skipTags.add('clippath');
    skipTags.add('mask');
    skipTags.add('defs');  // Skip defs entirely if not extracting clip paths
  }
  
  // Collect all referenceable elements (symbols, groups, etc.) from defs
  const defsElements = new Map();
  const collectDefs = (elem) => {
    for (const child of elem.children) {
      const id = child.getAttribute('id');
      if (id) {
        defsElements.set(id, child);
      }
      // Recurse into nested elements
      if (child.children.length > 0) {
        collectDefs(child);
      }
    }
  };
  // Collect from all defs elements
  for (const defs of svg.querySelectorAll('defs')) {
    collectDefs(defs);
  }
  // Also collect top-level elements with IDs (symbols can be outside defs)
  for (const child of svg.children) {
    const id = child.getAttribute('id');
    if (id && !defsElements.has(id)) {
      defsElements.set(id, child);
    }
  }

  // Parse embedded <style> blocks to resolve CSS class-based fill/stroke
  // This enables skipStrokeOnly to work with class-styled SVGs (common in design tool exports)
  const cssRules = new Map(); // selector -> { fill, stroke }
  for (const styleElem of svg.querySelectorAll('style')) {
    const cssText = styleElem.textContent || '';
    // Simple CSS parser: extract class selectors and their fill/stroke properties
    const ruleRegex = /([^{}]+)\{([^}]+)\}/g;
    let ruleMatch;
    while ((ruleMatch = ruleRegex.exec(cssText)) !== null) {
      const selector = ruleMatch[1].trim();
      const body = ruleMatch[2];
      const props = {};
      const fillMatch = body.match(/(?:^|;)\s*fill\s*:\s*([^;]+)/i);
      if (fillMatch) props.fill = fillMatch[1].trim();
      const strokeMatch = body.match(/(?:^|;)\s*stroke\s*:\s*([^;]+)/i);
      if (strokeMatch) props.stroke = strokeMatch[1].trim();
      if (props.fill || props.stroke) {
        cssRules.set(selector, props);
      }
    }
  }

  // Resolve effective fill/stroke for an element, checking inline attrs, style attr, and CSS classes
  function getEffectiveStyle(elem) {
    let fill = elem.getAttribute('fill');
    let stroke = elem.getAttribute('stroke');

    // Check inline style attribute (higher specificity)
    const style = elem.getAttribute('style') || '';
    const styleFill = style.match(/fill\s*:\s*([^;]+)/i)?.[1]?.trim();
    const styleStroke = style.match(/stroke\s*:\s*([^;]+)/i)?.[1]?.trim();
    if (styleFill) fill = styleFill;
    if (styleStroke) stroke = styleStroke;

    // Check CSS class rules if no inline fill/stroke found
    if (cssRules.size > 0 && (!fill || !stroke)) {
      const className = elem.getAttribute('class');
      if (className) {
        for (const cls of className.split(/\s+/)) {
          const rule = cssRules.get('.' + cls);
          if (rule) {
            if (!fill && rule.fill) fill = rule.fill;
            if (!stroke && rule.stroke) stroke = rule.stroke;
          }
        }
      }
    }

    return { fill, stroke };
  }

  // Helper to parse a value that might be a percentage or have units
  function parseValueWithPercent(value, referenceSize, fontSize = 16) {
    if (!value) return 0;
    const str = String(value).trim();
    
    if (str.endsWith('%')) {
      return (parseFloat(str) / 100) * referenceSize;
    }
    
    // Handle various SVG/CSS units
    // Conversion factors to user units (px at 96 DPI)
    const num = parseFloat(str) || 0;
    
    if (str.endsWith('px')) {
      return num;
    } else if (str.endsWith('pt')) {
      // 1pt = 1/72 inch = 96/72 px ≈ 1.333px
      return num * (96 / 72);
    } else if (str.endsWith('pc')) {
      // 1pc = 12pt = 16px
      return num * 16;
    } else if (str.endsWith('in')) {
      // 1in = 96px
      return num * 96;
    } else if (str.endsWith('cm')) {
      // 1cm = 96/2.54 px ≈ 37.795px
      return num * (96 / 2.54);
    } else if (str.endsWith('mm')) {
      // 1mm = 96/25.4 px ≈ 3.7795px
      return num * (96 / 25.4);
    } else if (str.endsWith('em')) {
      // 1em = current font-size
      return num * fontSize;
    } else if (str.endsWith('ex')) {
      // 1ex ≈ 0.5em (x-height approximation)
      return num * fontSize * 0.5;
    } else if (str.endsWith('rem')) {
      // 1rem = root font-size (assume 16px)
      return num * 16;
    }
    
    // No unit or unknown unit - treat as user units (px)
    return num;
  }
  
  // Determine the active layer name for an element, falling back to the parent layer
  function getLayerNameFromElement(elem, parentLayer) {
    const tag = elem.tagName?.toLowerCase() || '';
    const label = elem.getAttribute('inkscape:label');
    const groupMode = elem.getAttribute('inkscape:groupmode');
    const dataLayer = elem.getAttribute('data-layer') || elem.getAttribute('data-layer-name');
    const dataName = elem.getAttribute('data-name');
    const ariaLabel = elem.getAttribute('aria-label');
    const id = elem.getAttribute('id');

    // Explicit Inkscape layer
    if (groupMode === 'layer') {
      if (label && label.trim()) return label.trim();
      if (dataName && dataName.trim()) return dataName.trim();
      if (id && id.trim()) return id.trim();
    }

    // Illustrator exports often use id/data-name on the layer <g>
    if (tag === 'g') {
      if (dataLayer && dataLayer.trim()) return dataLayer.trim();
      if (dataName && dataName.trim()) return dataName.trim();
      if (ariaLabel && ariaLabel.trim()) return ariaLabel.trim();
      if (id && /^layer[\s_-]?/i.test(id.trim())) return id.trim();
    }

    return parentLayer || null;
  }

  function processElement(elem, parentTransform = '', insideClipOrMask = false, isRootSvg = false, refWidth = vbWidth, refHeight = vbHeight, currentLayer = null) {
    const tag = elem.tagName.toLowerCase();
    const layerName = getLayerNameFromElement(elem, currentLayer);
    
    // Skip namespace-prefixed elements (e.g., sodipodi:namedview, inkscape:grid)
    if (tag.includes(':')) {
      return;
    }
    
    // Skip marker, symbol, pattern, and filter elements entirely
    // Symbols are handled via <use> references, others are purely decorative
    if (tag === 'marker' || tag === 'symbol' || tag === 'pattern' || tag === 'filter') {
      return;
    }
    
    // Safety check: skip shapes that are inside marker/pattern/filter containers
    // (Symbols are OK - they get processed via <use> with proper transforms)
    let parent = elem.parentElement;
    while (parent) {
      const parentTag = parent.tagName?.toLowerCase();
      if (parentTag === 'marker' || parentTag === 'pattern' || parentTag === 'filter') {
        return; // Skip - we're inside a definition element that shouldn't produce shapes
      }
      if (parentTag === 'svg') break; // Reached root, we're safe
      parent = parent.parentElement;
    }
    
    // Track if we're inside a clipPath or mask
    const isClipOrMask = tag === 'clippath' || tag === 'mask';
    const isDefs = tag === 'defs';
    const isNestedSvg = tag === 'svg' && !isRootSvg;
    const nowInsideClipOrMask = insideClipOrMask || isClipOrMask;
    
    // Handle nested SVG elements - they have their own coordinate system
    if (isNestedSvg) {
      // Get nested SVG position and dimensions (may use percentages)
      const nestedX = parseValueWithPercent(elem.getAttribute('x'), refWidth);
      const nestedY = parseValueWithPercent(elem.getAttribute('y'), refHeight);
      const nestedWidth = parseValueWithPercent(elem.getAttribute('width'), refWidth);
      const nestedHeight = parseValueWithPercent(elem.getAttribute('height'), refHeight);
      
      // Skip if no valid dimensions
      if (nestedWidth <= 0 || nestedHeight <= 0) {
        return;
      }
      
      // Parse nested viewBox
      const nestedViewBox = elem.getAttribute('viewBox');
      let nvbX = 0, nvbY = 0, nvbWidth = nestedWidth, nvbHeight = nestedHeight;
      let hasViewBox = false;
      if (nestedViewBox) {
        const parts = nestedViewBox.split(/[\s,]+/).map(Number);
        if (parts.length >= 4) {
          [nvbX, nvbY, nvbWidth, nvbHeight] = parts;
          hasViewBox = true;
        }
      }
      
      // Skip if viewBox has no valid dimensions
      if (nvbWidth <= 0 || nvbHeight <= 0) {
        return;
      }
      
      let nestedTransform;
      
      if (!hasViewBox) {
        // No viewBox - just translate, no scaling needed
        nestedTransform = `translate(${nestedX}, ${nestedY})`;
      } else {
        // Has viewBox - apply preserveAspectRatio
        const par = elem.getAttribute('preserveAspectRatio') || 'xMidYMid meet';
        const parParts = par.trim().split(/\s+/);
        const align = parParts[0] || 'xMidYMid';
        const meetOrSlice = parParts[1] || 'meet';
        
        // Calculate scale factors
        const scaleX = nestedWidth / nvbWidth;
        const scaleY = nestedHeight / nvbHeight;
        
        let finalScaleX, finalScaleY, offsetX, offsetY;
        
        if (align === 'none') {
          // Non-uniform scaling
          finalScaleX = scaleX;
          finalScaleY = scaleY;
          offsetX = nestedX - nvbX * finalScaleX;
          offsetY = nestedY - nvbY * finalScaleY;
        } else {
          // Uniform scaling (meet or slice)
          const uniformScale = meetOrSlice === 'slice' 
            ? Math.max(scaleX, scaleY) 
            : Math.min(scaleX, scaleY);
          finalScaleX = uniformScale;
          finalScaleY = uniformScale;
          
          // Calculate alignment offsets
          const scaledWidth = nvbWidth * uniformScale;
          const scaledHeight = nvbHeight * uniformScale;
          
          // X alignment
          let xOffset = 0;
          if (align.includes('xMid')) {
            xOffset = (nestedWidth - scaledWidth) / 2;
          } else if (align.includes('xMax')) {
            xOffset = nestedWidth - scaledWidth;
          }
          // xMin is 0 (default)
          
          // Y alignment
          let yOffset = 0;
          if (align.includes('YMid')) {
            yOffset = (nestedHeight - scaledHeight) / 2;
          } else if (align.includes('YMax')) {
            yOffset = nestedHeight - scaledHeight;
          }
          // YMin is 0 (default)
          
          offsetX = nestedX + xOffset - nvbX * uniformScale;
          offsetY = nestedY + yOffset - nvbY * uniformScale;
        }
        
        // Build transform string
        if (finalScaleX === finalScaleY) {
          nestedTransform = `translate(${offsetX}, ${offsetY}) scale(${finalScaleX})`;
        } else {
          nestedTransform = `translate(${offsetX}, ${offsetY}) scale(${finalScaleX}, ${finalScaleY})`;
        }
      }
      
      // Combine with parent transform
      const combinedNestedTransform = parentTransform + ' ' + nestedTransform;
      
      // Process children with the combined transform and nested viewBox as reference for percentages
      for (const child of elem.children) {
        processElement(child, combinedNestedTransform, nowInsideClipOrMask, false, nvbWidth, nvbHeight, layerName);
      }
      return;
    }
    
    // Handle defs element
    if (isDefs) {
      if (extractClipPaths) {
        // When extracting clip paths, recurse into defs to find clippath/mask
        for (const child of elem.children) {
          processElement(child, parentTransform, false, false, refWidth, refHeight, layerName);
        }
      }
      // Always return after processing defs (don't extract defs as a shape)
      return;
    }
    
    // Handle clippath and mask elements
    if (isClipOrMask) {
      if (extractClipPaths) {
        // When extracting, recurse into clippath/mask to get the shapes inside
        for (const child of elem.children) {
          processElement(child, parentTransform, true, false, refWidth, refHeight, layerName);
        }
      }
      // Always return (clippath/mask itself is not a shape)
      return;
    }
    
    // Handle <use> elements - they reference other elements
    if (tag === 'use') {
      // Get the reference (href or xlink:href)
      let href = elem.getAttribute('href') || elem.getAttribute('xlink:href');
      if (!href || !href.startsWith('#')) {
        return; // Can't resolve external references
      }
      
      const refId = href.slice(1); // Remove '#'
      const refElem = defsElements.get(refId) || svg.querySelector(`#${CSS.escape(refId)}`);
      if (!refElem) {
        return; // Referenced element not found
      }
      
      // Get use element position and size
      const useX = parseFloat(elem.getAttribute('x') || 0);
      const useY = parseFloat(elem.getAttribute('y') || 0);
      const useWidth = parseFloat(elem.getAttribute('width') || 0);
      const useHeight = parseFloat(elem.getAttribute('height') || 0);
      const useTransform = elem.getAttribute('transform') || '';
      
      const refTag = refElem.tagName.toLowerCase();
      
      if (refTag === 'symbol') {
        // Symbol has its own viewBox - handle like nested SVG
        const symbolViewBox = refElem.getAttribute('viewBox');
        if (!symbolViewBox || useWidth <= 0 || useHeight <= 0) {
          // Can't render symbol without viewBox or dimensions
          return;
        }
        
        const vbParts = symbolViewBox.split(/[\s,]+/).map(Number);
        if (vbParts.length < 4) return;
        const [svbX, svbY, svbWidth, svbHeight] = vbParts;
        
        if (svbWidth <= 0 || svbHeight <= 0) return;
        
        // Calculate scale and offset (similar to nested SVG with meet)
        const scaleX = useWidth / svbWidth;
        const scaleY = useHeight / svbHeight;
        const uniformScale = Math.min(scaleX, scaleY);
        
        const scaledWidth = svbWidth * uniformScale;
        const scaledHeight = svbHeight * uniformScale;
        const xOffset = (useWidth - scaledWidth) / 2;
        const yOffset = (useHeight - scaledHeight) / 2;
        
        const offsetX = useX + xOffset - svbX * uniformScale;
        const offsetY = useY + yOffset - svbY * uniformScale;
        
        const symbolTransform = `translate(${offsetX}, ${offsetY}) scale(${uniformScale})`;
        const combinedUseTransform = parentTransform + ' ' + useTransform + ' ' + symbolTransform;
        
        // Process symbol children
        for (const child of refElem.children) {
          processElement(child, combinedUseTransform, nowInsideClipOrMask, false, svbWidth, svbHeight, layerName);
        }
      } else {
        // Other elements (g, path, rect, etc.) - just translate and process
        const useTranslate = `translate(${useX}, ${useY})`;
        const combinedUseTransform = parentTransform + ' ' + useTransform + ' ' + useTranslate;
        
        // Process the referenced element
        processElement(refElem, combinedUseTransform, nowInsideClipOrMask, false, refWidth, refHeight, layerName);
      }
      return;
    }
    
    // Handle <symbol> elements (skip if not being referenced by use)
    if (tag === 'symbol') {
      return; // Symbols are only rendered via <use>
    }
    
    // Skip other definition containers and non-shape elements
    if (skipTags.has(tag)) {
      return;
    }
    
    // Handle tags that should just recurse into children (like switch)
    if (recurseTags.has(tag)) {
      for (const child of elem.children) {
        processElement(child, parentTransform, nowInsideClipOrMask, false, refWidth, refHeight, layerName);
      }
      return;
    }
    
    const elemTransform = elem.getAttribute('transform') || '';
    const combinedTransform = parentTransform + ' ' + elemTransform;
    
    // Skip stroke-only elements if option is enabled
    // These are elements with fill="none" and a stroke - they're designed for line rendering
    // and won't render correctly as filled Resolume slices
    if (skipStrokeOnly) {
      const { fill: effectiveFill, stroke: effectiveStroke } = getEffectiveStyle(elem);

      // Skip if fill is "none" and there's a stroke
      if (effectiveFill === 'none' && effectiveStroke && effectiveStroke !== 'none') {
        return; // Skip this stroke-only element
      }
    }
    
    let points = [];
    let bezierData = null;
    let hasBezierCurves = false;
    
    // Get font-size for em unit calculations (default 16px)
    const elemFontSize = parseFloat(elem.getAttribute('font-size')) || 16;
    
    if (tag === 'path') {
      const d = elem.getAttribute('d');
      // Skip empty or whitespace-only paths
      if (d && d.trim()) {
        // Check for compound paths (multiple subpaths)
        const subpaths = splitCompoundPath(d);
        
        if (subpaths.length > 1) {
          // Compound path - process each subpath as a separate shape
          subpaths.forEach((subpathD, subpathIndex) => {
            const subPoints = parseSvgPath(subpathD, bezierResolution);
            const subBezierData = parseSvgPathWithBezier(subpathD);

            if (subPoints.length >= 3) {
              let processedPoints = applyTransform(subPoints, combinedTransform);
              processedPoints = processedPoints.map(p => ({ x: p.x - vbX, y: p.y - vbY }));
              
              let processedBezierData = null;
              if (subBezierData && subBezierData.points.length > 0) {
                let bezierPoints = subBezierData.points;
                bezierPoints = applyTransform(bezierPoints, combinedTransform);
                bezierPoints = bezierPoints.map(p => ({ x: p.x - vbX, y: p.y - vbY }));
                processedBezierData = { points: bezierPoints, segments: subBezierData.segments };
              }
              
              shapeCount++;
              
              // Generate shape name
              let baseName;
              const elemId = elem.getAttribute('id');
              const elemTitle = elem.querySelector('title')?.textContent?.trim();
              const friendlyTypes = {
                'path': 'Path',
                'rect': 'Rectangle',
                'circle': 'Circle',
                'ellipse': 'Ellipse',
                'polygon': 'Polygon',
                'polyline': 'Polyline',
                'g': 'Group'
              };
              
              if (useTitle && elemTitle) {
                baseName = useType ? `${elemTitle}_${friendlyTypes[tag] || tag}_${subpathIndex + 1}` : `${elemTitle}_${subpathIndex + 1}`;
              } else if (useTitle && elemId) {
                baseName = useType ? `${elemId}_${friendlyTypes[tag] || tag}_${subpathIndex + 1}` : `${elemId}_${subpathIndex + 1}`;
              } else if (useType) {
                baseName = `${friendlyTypes[tag] || tag}_${shapeCount}`;
              } else {
                baseName = `Shape_${shapeCount}`;
              }
              
              // Note: We used to deduplicate when first==last, but this caused issues
              // with bezier geometry. Resolume handles first==last correctly with closed="1"
              
              const bbox = {
                minX: Math.min(...processedPoints.map(p => p.x)),
                maxX: Math.max(...processedPoints.map(p => p.x)),
                minY: Math.min(...processedPoints.map(p => p.y)),
                maxY: Math.max(...processedPoints.map(p => p.y))
              };
              
              rawShapes.push({
                name: baseName,
                points: processedPoints,
                bezierData: processedBezierData,
                hasBezierCurves: subBezierData.hasBezier,
                bbox: bbox,
                sourceType: tag,
                isFromClipPath: nowInsideClipOrMask,
                isCompoundSubpath: true,
                subpathIndex: subpathIndex,
                layer: layerName
              });
            }
          });
          
          // Process children and return (we've already added shapes)
          for (const child of elem.children) {
            processElement(child, combinedTransform, nowInsideClipOrMask, false, refWidth, refHeight, layerName);
          }
          return;
        }
        
        // Single path - process normally
        points = parseSvgPath(d, bezierResolution);
        bezierData = parseSvgPathWithBezier(d);
        hasBezierCurves = bezierData.hasBezier;
      }
    } else if (tag === 'polygon' || tag === 'polyline') {
      const pts = elem.getAttribute('points');
      if (pts && pts.trim()) points = parsePolygonPoints(pts);
    } else if (tag === 'rect') {
      const x = parseValueWithPercent(elem.getAttribute('x'), refWidth, elemFontSize);
      const y = parseValueWithPercent(elem.getAttribute('y'), refHeight, elemFontSize);
      const w = parseValueWithPercent(elem.getAttribute('width'), refWidth, elemFontSize);
      const h = parseValueWithPercent(elem.getAttribute('height'), refHeight, elemFontSize);
      
      // Skip rects with zero or negative dimensions
      if (w <= 0 || h <= 0) {
        // Still process children
        for (const child of elem.children) {
          processElement(child, combinedTransform, nowInsideClipOrMask, false, refWidth, refHeight, layerName);
        }
        return;
      }
      
      let rx = parseValueWithPercent(elem.getAttribute('rx'), refWidth, elemFontSize);
      let ry = parseValueWithPercent(elem.getAttribute('ry'), refHeight, elemFontSize);
      
      if (rx && !ry) ry = rx;
      if (ry && !rx) rx = ry;
      rx = Math.min(rx, w / 2);
      ry = Math.min(ry, h / 2);
      
      if (rx > 0 && ry > 0) {
        const numCornerPoints = Math.max(Math.ceil(bezierResolution / 2), 4);
        
        // Check if this is a pill shape (corners meet with no straight edges)
        const hasHorizontalEdge = rx < w / 2;  // Has straight top/bottom edges
        const hasVerticalEdge = ry < h / 2;    // Has straight left/right edges
        
        // Top edge (only if there's a horizontal edge)
        if (hasHorizontalEdge) {
          points.push({ x: x + rx, y: y });
          points.push({ x: x + w - rx, y: y });
        } else {
          // Pill shape - just start at the top center
          points.push({ x: x + w / 2, y: y });
        }
        
        // Top-right corner (angle from -π/2 to 0)
        for (let i = 1; i <= numCornerPoints; i++) {
          const angle = -Math.PI / 2 + (Math.PI / 2) * (i / numCornerPoints);
          points.push({ x: x + w - rx + rx * Math.cos(angle), y: y + ry + ry * Math.sin(angle) });
        }
        
        // Right edge (only if there's a vertical edge)
        if (hasVerticalEdge) {
          points.push({ x: x + w, y: y + h - ry });
        }
        
        // Bottom-right corner (angle from 0 to π/2)
        for (let i = 1; i <= numCornerPoints; i++) {
          const angle = 0 + (Math.PI / 2) * (i / numCornerPoints);
          points.push({ x: x + w - rx + rx * Math.cos(angle), y: y + h - ry + ry * Math.sin(angle) });
        }
        
        // Bottom edge (only if there's a horizontal edge)
        if (hasHorizontalEdge) {
          points.push({ x: x + rx, y: y + h });
        }
        
        // Bottom-left corner (angle from π/2 to π)
        for (let i = 1; i <= numCornerPoints; i++) {
          const angle = Math.PI / 2 + (Math.PI / 2) * (i / numCornerPoints);
          points.push({ x: x + rx + rx * Math.cos(angle), y: y + h - ry + ry * Math.sin(angle) });
        }
        
        // Left edge (only if there's a vertical edge)
        if (hasVerticalEdge) {
          points.push({ x: x, y: y + ry });
        }
        
        // Top-left corner (angle from π to 3π/2) - but stop before the last point to avoid duplicate
        for (let i = 1; i < numCornerPoints; i++) {  // Note: < instead of <= to avoid duplicate closing point
          const angle = Math.PI + (Math.PI / 2) * (i / numCornerPoints);
          points.push({ x: x + rx + rx * Math.cos(angle), y: y + ry + ry * Math.sin(angle) });
        }
      } else {
        points = [
          { x: x, y: y },
          { x: x + w, y: y },
          { x: x + w, y: y + h },
          { x: x, y: y + h }
        ];
      }
    } else if (tag === 'circle') {
      const cx = parseValueWithPercent(elem.getAttribute('cx'), refWidth, elemFontSize);
      const cy = parseValueWithPercent(elem.getAttribute('cy'), refHeight, elemFontSize);
      // For radius, use the smaller of width/height as reference (per SVG spec)
      const r = parseValueWithPercent(elem.getAttribute('r'), Math.min(refWidth, refHeight), elemFontSize);
      
      // Skip circles with zero or negative radius
      if (r <= 0) {
        for (const child of elem.children) {
          processElement(child, combinedTransform, nowInsideClipOrMask, false, refWidth, refHeight, layerName);
        }
        return;
      }
      
      // Scale number of points based on circumference to ensure minimum segment length
      // Aim for segments of at least 1 pixel (was 2, but that's too aggressive for small circles)
      const circumference = 2 * Math.PI * r;
      const minSegmentLength = 1;
      const maxPoints = Math.max(bezierResolution * 4, 32);
      const pointsForSegmentLength = Math.floor(circumference / minSegmentLength);
      const numPoints = Math.max(12, Math.min(maxPoints, pointsForSegmentLength));
      
      for (let i = 0; i < numPoints; i++) {
        const angle = (i / numPoints) * Math.PI * 2;
        points.push({ x: cx + r * Math.cos(angle), y: cy + r * Math.sin(angle) });
      }
    } else if (tag === 'ellipse') {
      const cx = parseValueWithPercent(elem.getAttribute('cx'), refWidth, elemFontSize);
      const cy = parseValueWithPercent(elem.getAttribute('cy'), refHeight, elemFontSize);
      const rx = parseValueWithPercent(elem.getAttribute('rx'), refWidth, elemFontSize);
      const ry = parseValueWithPercent(elem.getAttribute('ry'), refHeight, elemFontSize);
      
      // Skip ellipses with zero or negative radii
      if (rx <= 0 || ry <= 0) {
        for (const child of elem.children) {
          processElement(child, combinedTransform, nowInsideClipOrMask, false, refWidth, refHeight, layerName);
        }
        return;
      }
      
      // Scale number of points based on circumference to ensure minimum segment length
      // Use approximation for ellipse circumference
      const avgRadius = (rx + ry) / 2;
      const circumference = 2 * Math.PI * avgRadius;
      const minSegmentLength = 1;
      const maxPoints = Math.max(bezierResolution * 4, 32);
      const pointsForSegmentLength = Math.floor(circumference / minSegmentLength);
      const numPoints = Math.max(12, Math.min(maxPoints, pointsForSegmentLength));
      
      for (let i = 0; i < numPoints; i++) {
        const angle = (i / numPoints) * Math.PI * 2;
        points.push({ x: cx + rx * Math.cos(angle), y: cy + ry * Math.sin(angle) });
      }
    } else if (tag === 'line') {
      const x1 = parseFloat(elem.getAttribute('x1') || 0);
      const y1 = parseFloat(elem.getAttribute('y1') || 0);
      const x2 = parseFloat(elem.getAttribute('x2') || 0);
      const y2 = parseFloat(elem.getAttribute('y2') || 0);
      points = [{ x: x1, y: y1 }, { x: x2, y: y2 }];
    }
    
    if (points.length >= 3) {  // Need at least 3 points for a valid polygon
      points = applyTransform(points, combinedTransform);
      // Adjust for viewBox origin
      points = points.map(p => ({ x: p.x - vbX, y: p.y - vbY }));
      
      // NOTE: Self-intersection splitting is disabled by default as it can cause issues
      // with complex paths that are intentionally self-intersecting (logos, icons, etc.)
      // The splitSelfIntersectingPolygon function is available if needed in the future.
      
      // Process bezier data similarly
      let processedBezierData = null;
      if (bezierData && bezierData.points.length > 0) {
        let bezierPoints = bezierData.points;
        bezierPoints = applyTransform(bezierPoints, combinedTransform);
        bezierPoints = bezierPoints.map(p => ({ x: p.x - vbX, y: p.y - vbY }));
        processedBezierData = { points: bezierPoints, segments: bezierData.segments };
      }
      
      shapeCount++;
      
      // Generate shape name based on naming mode
      let baseName;
      const elemId = elem.getAttribute('id');
      const elemTitle = elem.querySelector(':scope > title')?.textContent?.trim();
      
      // Build name parts based on enabled options
      const nameParts = [];
      
      if (useType) {
        const typeNames = {
          'rect': 'Rect',
          'circle': 'Circle',
          'ellipse': 'Ellipse',
          'polygon': 'Polygon',
          'polyline': 'Polyline',
          'path': 'Path',
          'line': 'Line'
        };
        const typeName = typeNames[tag] || tag.charAt(0).toUpperCase() + tag.slice(1);
        nameParts.push(`${typeName}_${shapeCount}`);
      }
      
      if (useTitle) {
        const titlePart = elemTitle || svgTitle || elemId;
        if (titlePart) {
          nameParts.push(titlePart);
        }
      }
      
      // Combine parts with dash, or use fallback
      if (nameParts.length > 0) {
        baseName = nameParts.join(' - ');
      } else {
        baseName = `Shape_${shapeCount}`;
      }
      
      // Add prefix for shapes extracted from clipPath/mask definitions
      const name = nowInsideClipOrMask ? `[Clip] ${baseName}` : baseName;
      
      // Track source element type to know if shape is supposed to be closed
      const sourceType = tag;
      
      rawShapes.push({ name, points, bezierData: processedBezierData, hasBezierCurves, sourceType, isFromClipPath: nowInsideClipOrMask, layer: layerName });
    }
    
    for (const child of elem.children) {
      processElement(child, combinedTransform, nowInsideClipOrMask, false, refWidth, refHeight, layerName);
    }
  }
  
  processElement(svg, '', false, true, vbWidth, vbHeight, null);  // true = this is the root SVG
  
  if (rawShapes.length === 0) return [];
  
  // Use all raw shapes
  const filteredRawShapes = rawShapes;
  
  if (filteredRawShapes.length === 0) return [];
  
  // Calculate actual content bounding box from shapes
  let contentMinX = Infinity, contentMinY = Infinity;
  let contentMaxX = -Infinity, contentMaxY = -Infinity;
  
  for (const shape of filteredRawShapes) {
    for (const p of shape.points) {
      contentMinX = Math.min(contentMinX, p.x);
      contentMinY = Math.min(contentMinY, p.y);
      contentMaxX = Math.max(contentMaxX, p.x);
      contentMaxY = Math.max(contentMaxY, p.y);
    }
  }
  
  const contentWidth = contentMaxX - contentMinX;
  const contentHeight = contentMaxY - contentMinY;
  
  // Calculate scale and offset
  let scale, offsetX, offsetY;
  
  if (scaleToFit && contentWidth > 0 && contentHeight > 0) {
    // Scale to fit actual content within available area
    const scaleX = availableWidth / contentWidth;
    const scaleY = availableHeight / contentHeight;
    scale = Math.min(scaleX, scaleY);
    
    // Center the scaled content
    offsetX = innerMargin + (availableWidth - contentWidth * scale) / 2 - contentMinX * scale;
    offsetY = innerMargin + (availableHeight - contentHeight * scale) / 2 - contentMinY * scale;
  } else {
    // No scaling - use 1:1 pixel mapping, center based on viewBox
    scale = 1;
    offsetX = innerMargin + (availableWidth - vbWidth) / 2;
    offsetY = innerMargin + (availableHeight - vbHeight) / 2;
  }
  
  // Second pass: apply scaling to all filtered shapes
  const shapes = [];
  
  for (const rawShape of filteredRawShapes) {
    let scaledPoints = rawShape.points.map(p => ({
      x: p.x * scale + offsetX,
      y: p.y * scale + offsetY
    }));
    
    // Auto-close open paths if option is enabled
    if (autoCloseOpenPaths && rawShape.sourceType === 'path' && scaledPoints.length >= 3) {
      const first = scaledPoints[0];
      const last = scaledPoints[scaledPoints.length - 1];
      const gap = Math.sqrt(Math.pow(first.x - last.x, 2) + Math.pow(first.y - last.y, 2));
      
      // If there's a significant gap, close the path by adding first point at end
      if (gap > 1) {
        scaledPoints = [...scaledPoints, { x: first.x, y: first.y }];
      }
    }
    
    let scaledBezierData = null;
    if (rawShape.bezierData && rawShape.bezierData.points.length > 0) {
      let scaledBezierPoints = rawShape.bezierData.points.map(p => ({
        x: p.x * scale + offsetX,
        y: p.y * scale + offsetY
      }));
      
      // Auto-close bezier data as well
      let updatedSegments = rawShape.bezierData.segments;
      if (autoCloseOpenPaths && rawShape.sourceType === 'path' && scaledBezierPoints.length >= 3) {
        const first = scaledBezierPoints[0];
        const last = scaledBezierPoints[scaledBezierPoints.length - 1];
        const gap = Math.sqrt(Math.pow(first.x - last.x, 2) + Math.pow(first.y - last.y, 2));
        
        if (gap > 1) {
          scaledBezierPoints = [...scaledBezierPoints, { x: first.x, y: first.y }];
          // Also add 'L' segment for the closing line
          updatedSegments = updatedSegments + 'L';
        }
      }
      
      scaledBezierData = { points: scaledBezierPoints, segments: updatedSegments };
    }
    
    // Note: We used to deduplicate when first==last, but this caused issues:
    // - Removing bezier segments broke curve geometry
    // - The actual problem (zero-length consecutive edges) was fixed in rect generation
    // Resolume handles first==last correctly with closed="1"
    
    // HOWEVER: We need to remove duplicate closing points for self-intersection detection
    // to work correctly. Only remove if last point is very close to first (< 0.5px)
    // and the shape is not a circle/ellipse (which naturally close)
    if (rawShape.sourceType !== 'circle' && rawShape.sourceType !== 'ellipse' && scaledPoints.length > 3) {
      const first = scaledPoints[0];
      const last = scaledPoints[scaledPoints.length - 1];
      const dist = Math.sqrt(Math.pow(last.x - first.x, 2) + Math.pow(last.y - first.y, 2));
      if (dist < 0.5) {
        scaledPoints = scaledPoints.slice(0, -1);
        // Also remove from bezier data if present
        if (scaledBezierData && scaledBezierData.points.length > 3) {
          const bzFirst = scaledBezierData.points[0];
          const bzLast = scaledBezierData.points[scaledBezierData.points.length - 1];
          const bzDist = Math.sqrt(Math.pow(bzLast.x - bzFirst.x, 2) + Math.pow(bzLast.y - bzFirst.y, 2));
          if (bzDist < 0.5) {
            scaledBezierData = {
              points: scaledBezierData.points.slice(0, -1),
              segments: scaledBezierData.segments.slice(0, -1)
            };
          }
        }
      }
    }
    
    const xs = scaledPoints.map(p => p.x);
    const ys = scaledPoints.map(p => p.y);
    
    const minX = Math.min(...xs);
    const minY = Math.min(...ys);
    const maxX = Math.max(...xs);
    const maxY = Math.max(...ys);
    
    shapes.push({
      name: rawShape.name,
      points: scaledPoints,
      bezierData: scaledBezierData,
      hasBezierCurves: rawShape.hasBezierCurves,
      sourceType: rawShape.sourceType,
      bbox: { minX, minY, maxX, maxY },
      isFromClipPath: rawShape.isFromClipPath,
      isCompoundSubpath: rawShape.isCompoundSubpath,
      subpathIndex: rawShape.subpathIndex,
      layer: rawShape.layer || null
    });
  }
  
  return shapes;
}

// Escape special XML characters in strings
function escapeXml(str) {
  if (typeof str !== 'string') return str;
  return str
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&apos;');
}

// Generate Polygon (Slice) XML
function generatePolygonXml(shape, uniqueId, customName = null) {
  const { bbox, name, sourceType } = shape;
  let outputPoints = [...shape.points]; // Create a copy
  const displayName = escapeXml(customName || name);
  
  // Validate bbox
  if (!bbox || !isFinite(bbox.minX) || !isFinite(bbox.minY) || !isFinite(bbox.maxX) || !isFinite(bbox.maxY)) {
    console.warn(`Shape "${displayName}" has invalid bounding box, skipping`);
    return null;
  }
  
  // Validate all points have finite coordinates
  if (outputPoints.some(p => !isFinite(p.x) || !isFinite(p.y))) {
    console.warn(`Shape "${displayName}" has invalid point coordinates, skipping`);
    return null;
  }
  
  // Remove duplicate closing point if first == last (causes zero-length edge with closed="1")
  // Skip this for circles/ellipses - they're generated without duplicate endpoints
  const skipClosingPointCheck = sourceType === 'circle' || sourceType === 'ellipse';
  
  if (!skipClosingPointCheck && outputPoints.length > 3) {
    const first = outputPoints[0];
    const last = outputPoints[outputPoints.length - 1];
    const dist = Math.sqrt(Math.pow(last.x - first.x, 2) + Math.pow(last.y - first.y, 2));
    if (dist < 0.5) { // Only remove if essentially the same point
      outputPoints = outputPoints.slice(0, -1);
    }
  }
  
  // Remove consecutive duplicate points (zero-length edges) - use small threshold
  let dedupedPoints = [outputPoints[0]];
  for (let i = 1; i < outputPoints.length; i++) {
    const prev = dedupedPoints[dedupedPoints.length - 1];
    const curr = outputPoints[i];
    const dist = Math.sqrt(Math.pow(curr.x - prev.x, 2) + Math.pow(curr.y - prev.y, 2));
    if (dist >= 0.01) { // Very small threshold - only remove true duplicates
      dedupedPoints.push(curr);
    }
  }
  
  outputPoints = dedupedPoints;
  
  // Merge very short edges that cause Resolume triangulation failures
  // Two passes:
  // 1. Remove truly sub-pixel edges (< 0.5px) regardless of angle - these can't be rendered
  // 2. Remove near-collinear points on edges < 1px - these cause triangulation issues
  
  // Pass 1: Remove sub-pixel edges unconditionally
  let filtered = [outputPoints[0]];
  for (let i = 1; i < outputPoints.length; i++) {
    const prev = filtered[filtered.length - 1];
    const curr = outputPoints[i];
    const dist = Math.sqrt(Math.pow(curr.x - prev.x, 2) + Math.pow(curr.y - prev.y, 2));
    if (dist >= 0.5) { // Keep edges >= 0.5px
      filtered.push(curr);
    }
  }
  // Also check closing edge
  if (filtered.length > 3) {
    const first = filtered[0];
    const last = filtered[filtered.length - 1];
    const closingDist = Math.sqrt(Math.pow(last.x - first.x, 2) + Math.pow(last.y - first.y, 2));
    if (closingDist < 0.5) {
      filtered = filtered.slice(0, -1);
    }
  }
  outputPoints = filtered;
  
  // Pass 2: Remove near-collinear points on short edges (< 1px but >= 0.5px)
  const MIN_EDGE_LENGTH = 1.0;
  let changed = true;
  let iterations = 0;
  const maxIterations = 10;
  
  while (changed && iterations < maxIterations && outputPoints.length > 4) {
    changed = false;
    iterations++;
    const newPoints = [];
    
    for (let i = 0; i < outputPoints.length; i++) {
      const prev = outputPoints[(i - 1 + outputPoints.length) % outputPoints.length];
      const curr = outputPoints[i];
      const next = outputPoints[(i + 1) % outputPoints.length];
      
      // Check edge length from prev to curr
      const edgeLen = Math.sqrt(Math.pow(curr.x - prev.x, 2) + Math.pow(curr.y - prev.y, 2));
      
      if (edgeLen < MIN_EDGE_LENGTH && newPoints.length > 0) {
        // Check if this is a corner (sharp angle) or collinear
        const v1 = { x: prev.x - curr.x, y: prev.y - curr.y };
        const v2 = { x: next.x - curr.x, y: next.y - curr.y };
        const len1 = Math.sqrt(v1.x * v1.x + v1.y * v1.y);
        const len2 = Math.sqrt(v2.x * v2.x + v2.y * v2.y);
        
        if (len1 > 0.001 && len2 > 0.001) {
          const dot = v1.x * v2.x + v1.y * v2.y;
          const cosAngle = Math.max(-1, Math.min(1, dot / (len1 * len2)));
          const angle = Math.acos(cosAngle) * 180 / Math.PI;
          
          // If angle > 160°, it's nearly collinear - safe to remove
          if (angle > 160) {
            changed = true;
            continue;
          }
        }
      }
      
      newPoints.push(curr);
    }
    
    if (changed && newPoints.length > 3) {
      outputPoints = newPoints;
    } else {
      changed = false;
    }
  }
  
  // Detect and remove degenerate "tail" patterns that cause self-intersection
  // Pattern: path returns to start point, then has a micro-triangle before closing
  // This is common in exported SVGs and causes Resolume rendering failures
  if (outputPoints.length > 10) {
    const startPoint = outputPoints[0];
    const threshold = 1.0; // 1 pixel tolerance
    
    // Find if any point near the end matches the start point
    // Search the last 5 points (not including the very last which might be a closing duplicate)
    for (let i = outputPoints.length - 5; i < outputPoints.length - 1; i++) {
      if (i < 3) continue; // Don't remove too many points
      const point = outputPoints[i];
      const distToStart = Math.sqrt(
        Math.pow(point.x - startPoint.x, 2) + 
        Math.pow(point.y - startPoint.y, 2)
      );
      
      if (distToStart < threshold) {
        // Found early return to start - remove this point and everything after
        console.log(`Removing degenerate tail from "${displayName}": cutting at point ${i}, removing ${outputPoints.length - i} points`);
        outputPoints = outputPoints.slice(0, i);
        break;
      }
    }
  }
  
  // Also check for points that are very close to the start anywhere in the last portion
  // This catches cases where the path spirals back multiple times
  if (outputPoints.length > 10) {
    const startPoint = outputPoints[0];
    const searchStart = Math.max(3, outputPoints.length - 15);
    
    for (let i = searchStart; i < outputPoints.length - 1; i++) {
      const point = outputPoints[i];
      const distToStart = Math.sqrt(
        Math.pow(point.x - startPoint.x, 2) + 
        Math.pow(point.y - startPoint.y, 2)
      );
      
      if (distToStart < 0.5) { // Very close to start - likely a duplicate
        // Check if remaining points form a micro-triangle
        const remaining = outputPoints.slice(i + 1);
        const remainingSpan = remaining.length > 0 ? Math.max(
          ...remaining.map(p => Math.sqrt(
            Math.pow(p.x - startPoint.x, 2) + 
            Math.pow(p.y - startPoint.y, 2)
          ))
        ) : 0;
        
        // If the remaining points stay within 2px of start, it's a degenerate tail
        if (remainingSpan < 2) {
          console.log(`Removing micro-tail from "${displayName}": ${outputPoints.length - i} points near start`);
          outputPoints = outputPoints.slice(0, i);
          break;
        }
      }
    }
  }
  
  // For very complex polygons (>200 points), apply Ramer-Douglas-Peucker simplification
  // This removes points that don't significantly affect the shape
  if (outputPoints.length > 200) {
    const rdpSimplify = (points, epsilon) => {
      if (points.length <= 2) return points;
      
      // Find point with maximum distance from line between first and last
      let maxDist = 0;
      let maxIdx = 0;
      const first = points[0];
      const last = points[points.length - 1];
      
      for (let i = 1; i < points.length - 1; i++) {
        // Perpendicular distance from point to line
        const dx = last.x - first.x;
        const dy = last.y - first.y;
        const len = Math.sqrt(dx * dx + dy * dy);
        
        let dist;
        if (len < 0.0001) {
          dist = Math.sqrt(Math.pow(points[i].x - first.x, 2) + Math.pow(points[i].y - first.y, 2));
        } else {
          dist = Math.abs(dy * points[i].x - dx * points[i].y + last.x * first.y - last.y * first.x) / len;
        }
        
        if (dist > maxDist) {
          maxDist = dist;
          maxIdx = i;
        }
      }
      
      // If max distance > epsilon, recursively simplify
      if (maxDist > epsilon) {
        const left = rdpSimplify(points.slice(0, maxIdx + 1), epsilon);
        const right = rdpSimplify(points.slice(maxIdx), epsilon);
        return [...left.slice(0, -1), ...right];
      } else {
        return [first, last];
      }
    };
    
    // Use epsilon of 0.5 pixels - removes points that deviate less than 0.5px from straight line
    const simplified = rdpSimplify(outputPoints, 0.5);
    
    // Only use simplified if it still has enough points
    if (simplified.length >= 3) {
      console.log(`Simplified "${displayName}" from ${outputPoints.length} to ${simplified.length} points`);
      outputPoints = simplified;
    }
  }
  
  // NOTE: Collinear point removal has been disabled because it can incorrectly
  // remove corner points in some SVGs. The low bezier resolution (3) is sufficient
  // to keep polygon complexity manageable for Resolume.
  
  // Expand short edges to minimum length for Resolume triangulation
  // Resolume can't triangulate edges < 1px, so we need to expand them
  // This preserves corners by moving points apart rather than removing them
  const MIN_EDGE_FOR_RESOLUME = 1.0;
  let expansionNeeded = true;
  let expansionIterations = 0;
  
  while (expansionNeeded && expansionIterations < 5 && outputPoints.length > 3) {
    expansionNeeded = false;
    expansionIterations++;
    
    for (let i = 0; i < outputPoints.length; i++) {
      const j = (i + 1) % outputPoints.length;
      const p1 = outputPoints[i];
      const p2 = outputPoints[j];
      
      const dx = p2.x - p1.x;
      const dy = p2.y - p1.y;
      const edgeLen = Math.sqrt(dx * dx + dy * dy);
      
      if (edgeLen > 0.001 && edgeLen < MIN_EDGE_FOR_RESOLUME) {
        // Need to expand this edge
        const scale = MIN_EDGE_FOR_RESOLUME / edgeLen;
        const midX = (p1.x + p2.x) / 2;
        const midY = (p1.y + p2.y) / 2;
        
        // Move points away from midpoint
        outputPoints[i] = {
          x: midX - (dx / 2) * scale,
          y: midY - (dy / 2) * scale
        };
        outputPoints[j] = {
          x: midX + (dx / 2) * scale,
          y: midY + (dy / 2) * scale
        };
        
        expansionNeeded = true;
      }
    }
  }
  
  // NOTE: Short edge removal has been disabled because it incorrectly removes
  // corner points in some SVGs. The low bezier resolution (3) is sufficient
  // to keep polygon complexity manageable for Resolume.
  // If Resolume still fails on specific shapes, try lowering bezier resolution further.
  
  // Ensure we still have at least 3 points after cleanup
  if (outputPoints.length < 3) {
    console.warn(`Shape "${displayName}" has fewer than 3 unique points after cleanup, skipping`);
    return null; // Signal to caller to skip this shape
  }
  
  // Check for degenerate (zero-area) bounding box
  const bboxWidth = bbox.maxX - bbox.minX;
  const bboxHeight = bbox.maxY - bbox.minY;
  if (bboxWidth < 0.01 || bboxHeight < 0.01) {
    console.warn(`Shape "${displayName}" has zero-area bounding box (${bboxWidth}x${bboxHeight}), skipping`);
    return null;
  }
  
  // Check for degenerate polygon using shoelace formula (area too small)
  // This catches collinear or nearly-collinear points that form invalid polygons
  let area = 0;
  for (let i = 0; i < outputPoints.length; i++) {
    const j = (i + 1) % outputPoints.length;
    area += outputPoints[i].x * outputPoints[j].y;
    area -= outputPoints[j].x * outputPoints[i].y;
  }
  area = Math.abs(area) / 2;
  
  if (area < 1) { // Less than 1 square pixel
    console.warn(`Shape "${displayName}" has degenerate area (${area.toFixed(4)} sq px), skipping`);
    return null;
  }
  
  const inputRectVerts = [
    { x: bbox.minX, y: bbox.minY },
    { x: bbox.maxX, y: bbox.minY },
    { x: bbox.maxX, y: bbox.maxY },
    { x: bbox.minX, y: bbox.maxY }
  ];
  
  // Round coordinates to 6 decimal places to avoid floating point issues
  const formatCoord = (n) => Number(n.toFixed(6));
  
  const vertsXml = (verts) => verts.map(v => 
    `\t\t\t\t\t\t\t<v x="${formatCoord(v.x)}" y="${formatCoord(v.y)}"/>`
  ).join('\n');
  
  // Compute points XML ONCE to ensure InputContour and OutputContour are identical
  const contourPointsXml = outputPoints.map(p => 
    `\t\t\t\t\t\t\t\t<v x="${formatCoord(p.x)}" y="${formatCoord(p.y)}"/>`
  ).join('\n');
  
  const segments = 'L'.repeat(outputPoints.length);
  
  // Verify segments count matches points count
  if (segments.length !== outputPoints.length) {
    console.warn(`Shape "${displayName}" segments/points mismatch: ${segments.length} vs ${outputPoints.length}`);
  }
  
  return `
\t\t\t\t\t<Polygon uniqueId="${uniqueId}" IsVirgin="0">
\t\t\t\t\t\t<Params name="Common">
\t\t\t\t\t\t\t<Param name="Name" T="STRING" default="Layer" value="${displayName}"/>
\t\t\t\t\t\t\t<Param name="Enabled" T="BOOL" default="1" value="1"/>
\t\t\t\t\t\t</Params>
\t\t\t\t\t\t<Params name="Input">
\t\t\t\t\t\t\t<ParamChoice name="Input Source" default="0:1" value="0:1" storeChoices="0"/>
\t\t\t\t\t\t\t<Param name="Input Opacity" T="BOOL" default="1" value="1"/>
\t\t\t\t\t\t\t<Param name="Input Bypass/Solo" T="BOOL" default="1" value="1"/>
\t\t\t\t\t\t</Params>
\t\t\t\t\t\t<Params name="Output">
\t\t\t\t\t\t\t<Param name="Flip" T="UINT8" default="0" value="0"/>
\t\t\t\t\t\t\t<ParamRange name="Brightness" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Contrast" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Red" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Green" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Blue" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<Param name="Is Key" T="BOOL" default="0" value="0"/>
\t\t\t\t\t\t\t<Param name="Black BG" T="BOOL" default="0" value="0"/>
\t\t\t\t\t\t</Params>
\t\t\t\t\t\t<InputRect orientation="0">
${vertsXml(inputRectVerts)}
\t\t\t\t\t\t</InputRect>
\t\t\t\t\t\t<OutputRect orientation="0">
${vertsXml(inputRectVerts)}
\t\t\t\t\t\t</OutputRect>
\t\t\t\t\t\t<InputContour closed="1">
\t\t\t\t\t\t\t<points>
${contourPointsXml}
\t\t\t\t\t\t\t</points>
\t\t\t\t\t\t\t<segments>${segments}</segments>
\t\t\t\t\t\t</InputContour>
\t\t\t\t\t\t<OutputContour closed="1">
\t\t\t\t\t\t\t<points>
${contourPointsXml}
\t\t\t\t\t\t\t</points>
\t\t\t\t\t\t\t<segments>${segments}</segments>
\t\t\t\t\t\t</OutputContour>
\t\t\t\t\t</Polygon>`;
}

// Generate Mask XML
function generateMaskXml(shape, uniqueId, customName = null, inverted = true, useBezierMode = false) {
  const { bbox, points, bezierData, name, sourceType } = shape;
  const rawName = customName || name;
  
  // Validate bbox
  if (!bbox || !isFinite(bbox.minX) || !isFinite(bbox.minY) || !isFinite(bbox.maxX) || !isFinite(bbox.maxY)) {
    console.warn(`Mask "${rawName}" has invalid bounding box, skipping`);
    return null;
  }
  
  // Validate all points have finite coordinates
  if (points.some(p => !isFinite(p.x) || !isFinite(p.y))) {
    console.warn(`Mask "${rawName}" has invalid point coordinates, skipping`);
    return null;
  }
  
  const displayName = escapeXml(rawName);
  
  // Check for degenerate (zero-area) bounding box
  const bboxWidth = bbox.maxX - bbox.minX;
  const bboxHeight = bbox.maxY - bbox.minY;
  if (bboxWidth < 0.01 || bboxHeight < 0.01) {
    console.warn(`Mask "${displayName}" has zero-area bounding box (${bboxWidth}x${bboxHeight}), skipping`);
    return null;
  }
  
  // Check for degenerate polygon using shoelace formula (area too small)
  let area = 0;
  for (let i = 0; i < points.length; i++) {
    const j = (i + 1) % points.length;
    area += points[i].x * points[j].y;
    area -= points[j].x * points[i].y;
  }
  area = Math.abs(area) / 2;
  
  if (area < 1) { // Less than 1 square pixel
    console.warn(`Mask "${displayName}" has degenerate area (${area.toFixed(4)} sq px), skipping`);
    return null;
  }
  
  // Round coordinates to 6 decimal places to avoid floating point issues
  const formatCoord = (n) => Number(n.toFixed(6));
  
  const vertsXml = (verts) => verts.map(v => 
    `\t\t\t\t\t\t\t<v x="${formatCoord(v.x)}" y="${formatCoord(v.y)}"/>`
  ).join('\n');
  
  const outputRectVerts = [
    { x: bbox.minX, y: bbox.minY },
    { x: bbox.maxX, y: bbox.minY },
    { x: bbox.maxX, y: bbox.maxY },
    { x: bbox.minX, y: bbox.maxY }
  ];
  
  const normalizedInputRect = [
    { x: -0.5, y: -0.5 },
    { x: 0.5, y: -0.5 },
    { x: 0.5, y: 0.5 },
    { x: -0.5, y: 0.5 }
  ];
  
  // Determine point mode and which points/segments to use
  let pointMode = "PM_LINEAR";
  let contourPoints = points;
  let segments = 'L'.repeat(points.length);
  
  if (useBezierMode && bezierData && bezierData.segments.includes('C')) {
    pointMode = "PM_BEZIER";
    contourPoints = bezierData.points;
    segments = bezierData.segments;
  }
  
  // Remove duplicate closing point if first == last (causes zero-length edge with closed="1")
  // Only do this for linear mode - bezier mode segments need to stay in sync with points
  // Skip this for circles/ellipses - they're generated without duplicate endpoints
  const skipClosingPointCheck = sourceType === 'circle' || sourceType === 'ellipse';
  if (pointMode === "PM_LINEAR" && !skipClosingPointCheck && contourPoints.length > 3) {
    const first = contourPoints[0];
    const last = contourPoints[contourPoints.length - 1];
    const dist = Math.sqrt(Math.pow(last.x - first.x, 2) + Math.pow(last.y - first.y, 2));
    if (dist < 0.5) { // Reduced threshold to 0.5 pixel to avoid false positives
      contourPoints = contourPoints.slice(0, -1);
    }
    
    // Also remove any consecutive duplicate points (zero-length edges)
    const dedupedPoints = [contourPoints[0]];
    for (let i = 1; i < contourPoints.length; i++) {
      const prev = dedupedPoints[dedupedPoints.length - 1];
      const curr = contourPoints[i];
      const d = Math.sqrt(Math.pow(curr.x - prev.x, 2) + Math.pow(curr.y - prev.y, 2));
      if (d >= 0.01) {
        dedupedPoints.push(curr);
      }
    }
    contourPoints = dedupedPoints;
    segments = 'L'.repeat(contourPoints.length);
  }
  
  // Ensure we still have at least 3 points after deduplication
  if (contourPoints.length < 3) {
    console.warn(`Mask "${displayName}" has fewer than 3 unique points after deduplication, skipping`);
    return null; // Signal to caller to skip this shape
  }
  
  // Compute points XML ONCE to ensure consistency
  const contourPointsXml = contourPoints.map(p => 
    `\t\t\t\t\t\t\t\t\t\t<v x="${formatCoord(p.x)}" y="${formatCoord(p.y)}"/>`
  ).join('\n');
  
  const invertValue = inverted ? "1" : "0";
  
  return `
\t\t\t\t\t<Mask uniqueId="${uniqueId}" IsVirgin="0">
\t\t\t\t\t\t<Params name="Common">
\t\t\t\t\t\t\t<Param name="Name" T="STRING" default="Layer" value="${displayName}_Mask"/>
\t\t\t\t\t\t\t<Param name="Enabled" T="BOOL" default="1" value="1"/>
\t\t\t\t\t\t</Params>
\t\t\t\t\t\t<Params name="Output">
\t\t\t\t\t\t\t<ParamRange name="Opacity" T="DOUBLE" default="1" value="1">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="0" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="0" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="0" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Feather" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="0" max="500"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="0" max="500"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="0" max="500"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Brightness" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Contrast" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Red" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Green" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Blue" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<Param name="Invert" T="BOOL" default="1" value="${invertValue}"/>
\t\t\t\t\t\t</Params>
\t\t\t\t\t\t<InputRect orientation="0">
${vertsXml(normalizedInputRect)}
\t\t\t\t\t\t</InputRect>
\t\t\t\t\t\t<OutputRect orientation="0">
${vertsXml(outputRectVerts)}
\t\t\t\t\t\t</OutputRect>
\t\t\t\t\t\t<ShapeObject>
\t\t\t\t\t\t\t<Params name="Shape">
\t\t\t\t\t\t\t\t<ParamChoice name="Point Mode" default="PM_LINEAR" value="${pointMode}" storeChoices="0"/>
\t\t\t\t\t\t\t</Params>
\t\t\t\t\t\t\t<Rect orientation="0">
${vertsXml(outputRectVerts)}
\t\t\t\t\t\t\t</Rect>
\t\t\t\t\t\t\t<Shape>
\t\t\t\t\t\t\t\t<Contour closed="1">
\t\t\t\t\t\t\t\t\t<points>
${contourPointsXml}
\t\t\t\t\t\t\t\t\t</points>
\t\t\t\t\t\t\t\t\t<segments>${segments}</segments>
\t\t\t\t\t\t\t\t</Contour>
\t\t\t\t\t\t\t</Shape>
\t\t\t\t\t\t</ShapeObject>
\t\t\t\t\t</Mask>`;
}

// Generate Combined Mask XML (multiple contours in one mask)
function generateCombinedMaskXml(shapes, uniqueId, colorName = null, inverted = true) {
  // Calculate combined bounding box
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  shapes.forEach(shape => {
    minX = Math.min(minX, shape.bbox.minX);
    minY = Math.min(minY, shape.bbox.minY);
    maxX = Math.max(maxX, shape.bbox.maxX);
    maxY = Math.max(maxY, shape.bbox.maxY);
  });
  
  const combinedBbox = { minX, minY, maxX, maxY };
  const name = escapeXml(colorName || 'Combined_Mask');
  const invertValue = inverted ? "1" : "0";
  
  // Round coordinates to 6 decimal places to avoid floating point issues
  const formatCoord = (n) => Number(n.toFixed(6));
  
  const vertsXml = (verts) => verts.map(v => 
    `\t\t\t\t\t\t\t<v x="${formatCoord(v.x)}" y="${formatCoord(v.y)}"/>`
  ).join('\n');
  
  const outputRectVerts = [
    { x: combinedBbox.minX, y: combinedBbox.minY },
    { x: combinedBbox.maxX, y: combinedBbox.minY },
    { x: combinedBbox.maxX, y: combinedBbox.maxY },
    { x: combinedBbox.minX, y: combinedBbox.maxY }
  ];
  
  const normalizedInputRect = [
    { x: -0.5, y: -0.5 },
    { x: 0.5, y: -0.5 },
    { x: 0.5, y: 0.5 },
    { x: -0.5, y: 0.5 }
  ];
  
  // Generate all contours
  const contoursXml = shapes.map(shape => {
    const shapePointsXml = shape.points.map(p => 
      `\t\t\t\t\t\t\t\t\t\t<v x="${formatCoord(p.x)}" y="${formatCoord(p.y)}"/>`
    ).join('\n');
    const segments = 'L'.repeat(shape.points.length);
    
    return `\t\t\t\t\t\t\t\t<Contour closed="1">
\t\t\t\t\t\t\t\t\t<points>
${shapePointsXml}
\t\t\t\t\t\t\t\t\t</points>
\t\t\t\t\t\t\t\t\t<segments>${segments}</segments>
\t\t\t\t\t\t\t\t</Contour>`;
  }).join('\n');
  
  return `
\t\t\t\t\t<Mask uniqueId="${uniqueId}" IsVirgin="0">
\t\t\t\t\t\t<Params name="Common">
\t\t\t\t\t\t\t<Param name="Name" T="STRING" default="Layer" value="${name}"/>
\t\t\t\t\t\t\t<Param name="Enabled" T="BOOL" default="1" value="1"/>
\t\t\t\t\t\t</Params>
\t\t\t\t\t\t<Params name="Output">
\t\t\t\t\t\t\t<ParamRange name="Opacity" T="DOUBLE" default="1" value="1">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="0" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="0" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="0" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Feather" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="0" max="500"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="0" max="500"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="0" max="500"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Brightness" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Contrast" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Red" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Green" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Blue" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<Param name="Invert" T="BOOL" default="1" value="${invertValue}"/>
\t\t\t\t\t\t</Params>
\t\t\t\t\t\t<InputRect orientation="0">
${vertsXml(normalizedInputRect)}
\t\t\t\t\t\t</InputRect>
\t\t\t\t\t\t<OutputRect orientation="0">
${vertsXml(outputRectVerts)}
\t\t\t\t\t\t</OutputRect>
\t\t\t\t\t\t<ShapeObject>
\t\t\t\t\t\t\t<Params name="Shape">
\t\t\t\t\t\t\t\t<ParamChoice name="Point Mode" default="PM_LINEAR" value="PM_LINEAR" storeChoices="0"/>
\t\t\t\t\t\t\t</Params>
\t\t\t\t\t\t\t<Rect orientation="0">
${vertsXml(outputRectVerts)}
\t\t\t\t\t\t\t</Rect>
\t\t\t\t\t\t\t<Shape>
${contoursXml}
\t\t\t\t\t\t\t</Shape>
\t\t\t\t\t\t</ShapeObject>
\t\t\t\t\t</Mask>`;
}

// Generate a single screen's XML
function generateScreenXml(screen, shapes, shapeSettings, combineMasks, uniqueIdBase, layerVisibility) {
  const screenWidth = screen.width || 3840;
  const screenHeight = screen.height || 2160;
  
  let layersXml = '';
  let idOffset = 0;

  const isLayerEnabled = (layerName) => {
    const key = layerName || 'Unlayered';
    return layerVisibility?.[key] !== false;
  };
  
  // Filter shapes for this screen
  const screenShapes = shapes.map((shape, i) => ({ shape, index: i }))
    .filter(({ index }) => {
      const settings = shapeSettings[index];
      const layerOn = isLayerEnabled(shapes[index]?.layer);
      return settings?.enabled && layerOn && settings?.screen === screen.id;
    });
  
  // Collect shapes that should be masks for potential combining
  const maskShapes = [];
  const maskInverted = []; // Track inverted state for combined masks
  
  screenShapes.forEach(({ shape, index }) => {
    const settings = shapeSettings[index];
    const customName = settings.customName || null;
    
    if (settings.slice) {
      const sliceXml = generatePolygonXml(shape, uniqueIdBase + idOffset, customName);
      if (sliceXml) {
        layersXml += sliceXml;
        idOffset++;
      }
    }
    
    if (settings.mask) {
      if (combineMasks) {
        // Only add to combined masks if it has enough points
        if (shape.points.length >= 3) {
          maskShapes.push(shape);
          maskInverted.push(settings.invertMask !== false); // Default to true
        }
      } else {
        const inverted = settings.invertMask !== false; // Default to true
        const useBezierMode = settings.bezierMode && shape.hasBezierCurves;
        const maskXml = generateMaskXml(shape, uniqueIdBase + idOffset, customName, inverted, useBezierMode);
        if (maskXml) {
          layersXml += maskXml;
          idOffset++;
        }
      }
    }
  });
  
  // Add combined mask if enabled and there are mask shapes
  // For combined masks, use inverted=true if ANY mask is inverted
  if (combineMasks && maskShapes.length > 0) {
    const anyInverted = maskInverted.some(inv => inv);
    layersXml += generateCombinedMaskXml(maskShapes, uniqueIdBase + idOffset, null, anyInverted);
    idOffset++;
  }
  
  const screenUniqueId = 1765633229473 + screen.id;
  
  return {
    xml: `
\t\t\t<Screen name="${screen.name}" uniqueId="${screenUniqueId}">
\t\t\t\t<Params name="Params">
\t\t\t\t\t<Param name="Name" T="STRING" default="" value="${screen.name}"/>
\t\t\t\t\t<Param name="Enabled" T="BOOL" default="1" value="1"/>
\t\t\t\t\t<Param name="Hidden" T="BOOL" default="0" value="0"/>
\t\t\t\t</Params>
\t\t\t\t<Params name="Output">
\t\t\t\t\t<ParamRange name="Opacity" T="DOUBLE" default="1" value="1">
\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t<ValueRange name="defaultRange" min="0" max="1"/>
\t\t\t\t\t\t<ValueRange name="minMax" min="0" max="1"/>
\t\t\t\t\t\t<ValueRange name="startStop" min="0" max="1"/>
\t\t\t\t\t</ParamRange>
\t\t\t\t\t<ParamRange name="Brightness" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t</ParamRange>
\t\t\t\t\t<ParamRange name="Contrast" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t</ParamRange>
\t\t\t\t\t<ParamRange name="Red" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t</ParamRange>
\t\t\t\t\t<ParamRange name="Green" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t</ParamRange>
\t\t\t\t\t<ParamRange name="Blue" T="DOUBLE" default="0" value="0">
\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t<ValueRange name="defaultRange" min="-1" max="1"/>
\t\t\t\t\t\t<ValueRange name="minMax" min="-1" max="1"/>
\t\t\t\t\t\t<ValueRange name="startStop" min="-1" max="1"/>
\t\t\t\t\t</ParamRange>
\t\t\t\t</Params>
\t\t\t\t<guides>
\t\t\t\t\t<ScreenGuide name="ScreenGuide" type="0">
\t\t\t\t\t\t<Params name="Params">
\t\t\t\t\t\t\t<ParamPixels name="Image"/>
\t\t\t\t\t\t\t<ParamRange name="Opacity" T="DOUBLE" default="0.25" value="0.25">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="0" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="0" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="0" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t</Params>
\t\t\t\t\t</ScreenGuide>
\t\t\t\t\t<ScreenGuide name="ScreenGuide" type="1">
\t\t\t\t\t\t<Params name="Params">
\t\t\t\t\t\t\t<ParamPixels name="Image"/>
\t\t\t\t\t\t\t<ParamRange name="Opacity" T="DOUBLE" default="0.25" value="0.25">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="0" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="0" max="1"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="0" max="1"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t</Params>
\t\t\t\t\t</ScreenGuide>
\t\t\t\t</guides>
\t\t\t\t<layers>${layersXml}
\t\t\t\t</layers>
\t\t\t\t<OutputDevice>
\t\t\t\t\t<OutputDeviceVirtual name="${screen.name}" deviceId="VirtualScreen ${screen.id}" idHash="${10094742552620344504 + screen.id}" width="${screenWidth}" height="${screenHeight}">
\t\t\t\t\t\t<Params name="Params">
\t\t\t\t\t\t\t<ParamRange name="Width" T="DOUBLE" default="1920" value="${screenWidth}">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="1" max="16384"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="1" max="16384"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="1" max="16384"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t\t<ParamRange name="Height" T="DOUBLE" default="1080" value="${screenHeight}">
\t\t\t\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t\t\t\t<ValueRange name="defaultRange" min="1" max="16384"/>
\t\t\t\t\t\t\t\t<ValueRange name="minMax" min="1" max="16384"/>
\t\t\t\t\t\t\t\t<ValueRange name="startStop" min="1" max="16384"/>
\t\t\t\t\t\t\t</ParamRange>
\t\t\t\t\t\t</Params>
\t\t\t\t\t</OutputDeviceVirtual>
\t\t\t\t</OutputDevice>
\t\t\t</Screen>`,
    idOffset
  };
}

function generateResolumeXML(shapes, shapeSettings, screens, name, canvasWidth, canvasHeight, combineMasks = false, layerVisibility = {}) {
  const uniqueIdBase = 1765633229505;
  
  // Generate XML for each screen that has shapes
  let screensXml = '';
  let totalIdOffset = 0;
  
  screens.forEach(screen => {
    // Check if this screen has any enabled shapes
    const hasShapes = shapes.some((shape, i) => {
      const settings = shapeSettings[i];
      const layerName = shape?.layer || 'Unlayered';
      const layerOn = layerVisibility[layerName] !== false;
      return settings?.enabled && layerOn && settings?.screen === screen.id && (settings?.slice || settings?.mask);
    });
    
    if (hasShapes) {
      const result = generateScreenXml(screen, shapes, shapeSettings, combineMasks, uniqueIdBase + totalIdOffset, layerVisibility);
      screensXml += result.xml;
      totalIdOffset += result.idOffset;
    }
  });
  
  return `<?xml version="1.0" encoding="utf-8"?>
<XmlState name="${name}">
\t<versionInfo name="Resolume Arena" majorVersion="7" minorVersion="23" microVersion="2" revision="51094"/>
\t<ScreenSetup name="ScreenSetup">
\t\t<Params name="ScreenSetupParams"/>
\t\t<CurrentCompositionTextureSize width="${canvasWidth}" height="${canvasHeight}"/>
\t\t<screens>${screensXml}
\t\t</screens>
\t\t<SoftEdging>
\t\t\t<Params name="Soft Edge">
\t\t\t\t<ParamRange name="Gamma Red" T="DOUBLE" default="2" value="2">
\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t<ValueRange name="defaultRange" min="1" max="3"/>
\t\t\t\t\t<ValueRange name="minMax" min="1" max="3"/>
\t\t\t\t\t<ValueRange name="startStop" min="1" max="3"/>
\t\t\t\t</ParamRange>
\t\t\t\t<ParamRange name="Gamma Green" T="DOUBLE" default="2" value="2">
\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t<ValueRange name="defaultRange" min="1" max="3"/>
\t\t\t\t\t<ValueRange name="minMax" min="1" max="3"/>
\t\t\t\t\t<ValueRange name="startStop" min="1" max="3"/>
\t\t\t\t</ParamRange>
\t\t\t\t<ParamRange name="Gamma Blue" T="DOUBLE" default="2" value="2">
\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t<ValueRange name="defaultRange" min="1" max="3"/>
\t\t\t\t\t<ValueRange name="minMax" min="1" max="3"/>
\t\t\t\t\t<ValueRange name="startStop" min="1" max="3"/>
\t\t\t\t</ParamRange>
\t\t\t\t<ParamRange name="Gamma" T="DOUBLE" default="1" value="1">
\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t<ValueRange name="defaultRange" min="0" max="1"/>
\t\t\t\t\t<ValueRange name="minMax" min="0" max="1"/>
\t\t\t\t\t<ValueRange name="startStop" min="0" max="1"/>
\t\t\t\t</ParamRange>
\t\t\t\t<ParamRange name="Luminance" T="DOUBLE" default="0.5" value="0.5">
\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t<ValueRange name="defaultRange" min="0" max="1"/>
\t\t\t\t\t<ValueRange name="minMax" min="0" max="1"/>
\t\t\t\t\t<ValueRange name="startStop" min="0" max="1"/>
\t\t\t\t</ParamRange>
\t\t\t\t<ParamRange name="Power" T="DOUBLE" default="2" value="2">
\t\t\t\t\t<PhaseSourceStatic name="PhaseSourceStatic"/>
\t\t\t\t\t<BehaviourDouble name="BehaviourDouble"/>
\t\t\t\t\t<ValueRange name="defaultRange" min="0.1" max="7"/>
\t\t\t\t\t<ValueRange name="minMax" min="0.1" max="7"/>
\t\t\t\t\t<ValueRange name="startStop" min="0.1" max="7"/>
\t\t\t\t</ParamRange>
\t\t\t</Params>
\t\t</SoftEdging>
\t</ScreenSetup>
</XmlState>
`;
}

function Svg2XmlApp() {
  const [svgText, setSvgText] = useState('');
  const [fileName, setFileName] = useState('');
  const [shapes, setShapes] = useState([]);
  const [shapeSettings, setShapeSettings] = useState({}); // Per-shape settings: { [index]: { slice: bool, mask: bool, enabled: bool, screen: number } }
  const [layerVisibility, setLayerVisibility] = useState({});
  const fallbackLayerName = 'Unlayered';
  const [shapesLayerFilter, setShapesLayerFilter] = useState('visible'); // 'visible' | 'all'

  // Fade out the boot splash once the app mounts
  useEffect(() => {
    const splash = document.getElementById('boot-splash');
    if (splash) {
      splash.classList.add('boot-splash--fade');
      setTimeout(() => splash.remove(), 240);
    }
  }, []);
  // Helper to get default canvas size from localStorage
  const getDefaultCanvasSize = () => {
    try {
      const saved = localStorage.getItem('resolume-default-canvas-size');
      if (saved) {
        const parsed = JSON.parse(saved);
        if (parsed.width && parsed.height) {
          return parsed;
        }
      }
    } catch (e) {
      // Ignore localStorage errors
    }
    return { width: 3840, height: 2160 };
  };
  
  const initialDefault = getDefaultCanvasSize();
  const [screens, setScreens] = useState([{ id: 1, name: 'Screen 1', width: initialDefault.width, height: initialDefault.height }]);
  const [canvasWidth, setCanvasWidth] = useState(initialDefault.width);
  const [canvasHeight, setCanvasHeight] = useState(initialDefault.height);
  const [defaultCanvasSize, setDefaultCanvasSize] = useState(initialDefault);
  const [innerMargin, setInnerMargin] = useState(0);
  const [scaleToFit, setScaleToFit] = useState(false);
  const [extractClipPaths, setExtractClipPaths] = useState(false);
  const [autoCloseOpenPaths, setAutoCloseOpenPaths] = useState(false);
  const [skipStrokeOnly, setSkipStrokeOnly] = useState(false);
  const [useArtboard, setUseArtboard] = useState(() => {
    try {
      const saved = localStorage.getItem('resolume-use-artboard');
      return saved ? JSON.parse(saved) : true;
    } catch (e) { return true; }
  });
  const [shapeNameMode, setShapeNameMode] = useState({ type: true, title: false }); // Can enable both
  const [bezierResolution, setBezierResolution] = useState(5);
  const [defaultOutputType, setDefaultOutputType] = useState('slice');
  const [combineMasks, setCombineMasks] = useState(false);
  const [projectName, setProjectName] = useState('');
  const [documentTitle, setDocumentTitle] = useState(''); // Title from XMP/SVG metadata
  const [customProjectName, setCustomProjectName] = useState(''); // User-typed custom name
  const [nameSource, setNameSource] = useState('title'); // 'title', 'filename', or 'custom'
  const fileInputRef = useRef(null);
  const projectInputRef = useRef(null);
  
  
  
  
  // Save default canvas size to localStorage when it changes
  useEffect(() => {
    try {
      localStorage.setItem('resolume-default-canvas-size', JSON.stringify(defaultCanvasSize));
    } catch (e) {
      // Ignore localStorage errors
    }
  }, [defaultCanvasSize]);
  
  // Preview viewport state
  const [previewZoom, setPreviewZoom] = useState(1);
  const [previewPan, setPreviewPan] = useState({ x: 0, y: 0 });
  const [isTrackingEnabled, setIsTrackingEnabled] = useState(false);
  const [showPointNumbers, setShowPointNumbers] = useState(true); // Toggle point numbers on selected shapes
  const [lastSelectedShape, setLastSelectedShape] = useState(null);
  const [previewSelectedShape, setPreviewSelectedShape] = useState(null);
  const [selectionFilter, setSelectionFilter] = useState({ slice: true, mask: true, flagged: true });
  const [isPanning, setIsPanning] = useState(false);
  const [panStart, setPanStart] = useState({ mouseX: 0, mouseY: 0, panX: 0, panY: 0 });
  const previewContainerRef = useRef(null);
  const shapesTableRef = useRef(null);

  // Clear selection when its layer is hidden
  useEffect(() => {
    if (previewSelectedShape !== null) {
      const shape = shapes[previewSelectedShape];
      if (shape && !isLayerEnabled(shape.layer)) {
        setPreviewSelectedShape(null);
        setLastSelectedShape(null);
      }
    }
  }, [previewSelectedShape, shapes, isLayerEnabled]);
  
  
  // Point editing state
  const [editingPoint, setEditingPoint] = useState(null); // { shapeIndex, pointIndex }
  const [isDraggingPoint, setIsDraggingPoint] = useState(false);
  const [dragOffset, setDragOffset] = useState({ x: 0, y: 0 }); // Offset from mouse to point center
  const [floatingNameEditor, setFloatingNameEditor] = useState(null); // { shapeIndex, rect } for popup name editing

  // Theme state - 'dark' or 'light'
  const [theme, setTheme] = useState(() => {
    try {
      const saved = localStorage.getItem('resolume-theme');
      return saved || 'light';
    } catch (e) { return 'light'; }
  });

  // Layer stats derived from shapes + per-layer visibility controls
  const layerStats = useMemo(() => {
    const stats = new Map();
    shapes.forEach((shape, i) => {
      const layerName = shape?.layer || fallbackLayerName;
      const settings = shapeSettings[i] || { enabled: true, slice: true, mask: false };
      const entry = stats.get(layerName) || { total: 0, enabled: 0, slices: 0, masks: 0 };
      entry.total += 1;
      if (settings.enabled) {
        entry.enabled += 1;
        if (settings.slice) entry.slices += 1;
        if (settings.mask) entry.masks += 1;
      }
      stats.set(layerName, entry);
    });
    return Array.from(stats.entries()).map(([name, data]) => ({ name, ...data })).sort((a, b) => a.name.localeCompare(b.name));
  }, [shapes, shapeSettings, isLayerEnabled]);

  // Keep layerVisibility in sync with the layers present in the document
  useEffect(() => {
    if (layerStats.length === 0) {
      setLayerVisibility({});
      return;
    }
    const names = layerStats.map(l => l.name);
    setLayerVisibility(prev => {
      const next = {};
      let changed = false;
      names.forEach(name => {
        if (Object.prototype.hasOwnProperty.call(prev, name)) {
          next[name] = prev[name];
        } else {
          next[name] = true;
          changed = true;
        }
      });
      Object.keys(prev).forEach(k => {
        if (!names.includes(k)) changed = true;
      });
      return changed ? next : prev;
    });
  }, [layerStats]);

  const isLayerEnabled = useCallback((layerName) => {
    const key = layerName || fallbackLayerName;
    return layerVisibility[key] !== false;
  }, [layerVisibility]);

  const toggleLayerVisibility = useCallback((layerName) => {
    const key = layerName || fallbackLayerName;
    setLayerVisibility(prev => ({
      ...prev,
      [key]: !(prev[key] !== false)
    }));
  }, [fallbackLayerName]);

  const setAllLayersVisibility = useCallback((enabled) => {
    setLayerVisibility(prev => {
      const next = {};
      layerStats.forEach(layer => { next[layer.name] = enabled; });
      return next;
    });
  }, [layerStats]);
  
  // Save theme to localStorage when it changes
  useEffect(() => {
    try {
      localStorage.setItem('resolume-theme', theme);
    } catch (e) {
      // Ignore localStorage errors
    }
    // Toggle body class for CSS hover effects
    if (theme === 'light') {
      document.body.classList.add('light-theme', 'p-light');
      document.body.classList.remove('p-dark');
    } else {
      document.body.classList.remove('light-theme', 'p-light');
      document.body.classList.add('p-dark');
    }
  }, [theme]);
  
  // Get themed styles based on current theme
  const themeStyles = getThemedStyles(theme);
  
  // Section IDs for ordering and collapsing
  const defaultSectionOrder = ['preview', 'project', 'import', 'canvas', 'screens', 'layers', 'shapes'];
  
  // Default column assignments (left: preview/project; right: canvas/screens/import/shapes)
  const defaultSectionColumns = {
    // Left column
    preview: 'left',
    project: 'left',
    // Right column
    canvas: 'right',
    screens: 'right',
    import: 'right',
    layers: 'right',
    shapes: 'right'
  };
  
  // UI layout state with localStorage persistence
  const [collapsedSections, setCollapsedSections] = useState(() => {
    try {
      const saved = localStorage.getItem('resolume-collapsed-sections');
      if (saved) return JSON.parse(saved);
    } catch (e) {}
    return {};
  });
  
  const [sectionOrder, setSectionOrder] = useState(() => {
    try {
      const saved = localStorage.getItem('resolume-section-order');
      if (saved) {
        const parsed = JSON.parse(saved);
        if (Array.isArray(parsed)) {
          const filtered = parsed.filter(s => defaultSectionOrder.includes(s));
          // Validate that all sections are present
          if (defaultSectionOrder.every(s => filtered.includes(s))) {
            return filtered;
          }
        }
      }
    } catch (e) {}
    return defaultSectionOrder;
  });
  
  const [sectionColumns, setSectionColumns] = useState(() => {
    try {
      const saved = localStorage.getItem('resolume-section-columns');
      if (saved) {
        const parsed = JSON.parse(saved);
        if (typeof parsed === 'object') {
          const filtered = {};
          defaultSectionOrder.forEach(s => {
            filtered[s] = parsed[s] || defaultSectionColumns[s];
          });
          // Validate all sections have column assignment
          if (defaultSectionOrder.every(s => filtered[s])) {
            return filtered;
          }
        }
      }
    } catch (e) {}
    return defaultSectionColumns;
  });
  
  const [sideBySidePreview, setSideBySidePreview] = useState(() => {
    try {
      const saved = localStorage.getItem('resolume-side-by-side');
      if (saved) return JSON.parse(saved);
    } catch (e) {}
    return true;
  });
  
  const [previewSpanColumns, setPreviewSpanColumns] = useState(() => {
    try {
      const saved = localStorage.getItem('resolume-preview-span');
      if (saved) return JSON.parse(saved);
    } catch (e) {}
    return false;
  });

  // Apply new default layout (light + side-by-side with new column split) once per version
  const layoutVersion = '2026-03-23-layout-v6-layers';
  useEffect(() => {
    try {
      const savedVersion = localStorage.getItem('resolume-layout-version');
      if (savedVersion !== layoutVersion) {
        setSectionOrder(defaultSectionOrder);
        setSectionColumns(defaultSectionColumns);
        setSideBySidePreview(true);
        setPreviewSpanColumns(false);
        localStorage.setItem('resolume-layout-version', layoutVersion);
      }
    } catch (e) {
      // ignore
    }
  }, []);
  
  const [savedLayout, setSavedLayout] = useState(() => {
    try {
      const saved = localStorage.getItem('resolume-saved-layout');
      if (saved) return JSON.parse(saved);
    } catch (e) {}
    return null;
  });
  
  const [draggedSection, setDraggedSection] = useState(null);
  
  // Undo/Redo history system
  const [undoHistory, setUndoHistory] = useState([]);
  const [redoHistory, setRedoHistory] = useState([]);
  const isUndoRedoAction = useRef(false);
  
  // Save current state to undo history
  const saveToHistory = useCallback(() => {
    if (isUndoRedoAction.current) {
      isUndoRedoAction.current = false;
      return;
    }
    
    const currentState = {
      shapes: JSON.parse(JSON.stringify(shapes)),
      shapeSettings: JSON.parse(JSON.stringify(shapeSettings)),
      screens: JSON.parse(JSON.stringify(screens)),
      canvasWidth,
      canvasHeight,
      innerMargin,
      projectName,
      customProjectName,
      nameSource
    };
    
    setUndoHistory(prev => {
      const newHistory = [...prev, currentState];
      if (newHistory.length > 50) {
        return newHistory.slice(-50);
      }
      return newHistory;
    });
    
    setRedoHistory([]);
  }, [shapes, shapeSettings, screens, canvasWidth, canvasHeight, innerMargin, projectName, customProjectName, nameSource]);
  
  // Undo function
  const performUndo = useCallback(() => {
    if (undoHistory.length === 0) return;
    
    const currentState = {
      shapes: JSON.parse(JSON.stringify(shapes)),
      shapeSettings: JSON.parse(JSON.stringify(shapeSettings)),
      screens: JSON.parse(JSON.stringify(screens)),
      canvasWidth,
      canvasHeight,
      innerMargin,
      projectName,
      customProjectName,
      nameSource
    };
    setRedoHistory(prev => [...prev, currentState]);
    
    const previousState = undoHistory[undoHistory.length - 1];
    isUndoRedoAction.current = true;
    
    setShapes(previousState.shapes);
    setShapeSettings(previousState.shapeSettings);
    setScreens(previousState.screens);
    setCanvasWidth(previousState.canvasWidth);
    setCanvasHeight(previousState.canvasHeight);
    setInnerMargin(previousState.innerMargin);
    setProjectName(previousState.projectName);
    setCustomProjectName(previousState.customProjectName);
    setNameSource(previousState.nameSource);
    
    setUndoHistory(prev => prev.slice(0, -1));
  }, [undoHistory, shapes, shapeSettings, screens, canvasWidth, canvasHeight, innerMargin, projectName, customProjectName, nameSource]);
  
  // Redo function
  const performRedo = useCallback(() => {
    if (redoHistory.length === 0) return;
    
    const currentState = {
      shapes: JSON.parse(JSON.stringify(shapes)),
      shapeSettings: JSON.parse(JSON.stringify(shapeSettings)),
      screens: JSON.parse(JSON.stringify(screens)),
      canvasWidth,
      canvasHeight,
      innerMargin,
      projectName,
      customProjectName,
      nameSource
    };
    setUndoHistory(prev => [...prev, currentState]);
    
    const nextState = redoHistory[redoHistory.length - 1];
    isUndoRedoAction.current = true;
    
    setShapes(nextState.shapes);
    setShapeSettings(nextState.shapeSettings);
    setScreens(nextState.screens);
    setCanvasWidth(nextState.canvasWidth);
    setCanvasHeight(nextState.canvasHeight);
    setInnerMargin(nextState.innerMargin);
    setProjectName(nextState.projectName);
    setCustomProjectName(nextState.customProjectName);
    setNameSource(nextState.nameSource);
    
    setRedoHistory(prev => prev.slice(0, -1));
  }, [redoHistory, shapes, shapeSettings, screens, canvasWidth, canvasHeight, innerMargin, projectName, customProjectName, nameSource]);
  
  // Global keyboard shortcuts for undo/redo
  useEffect(() => {
    const handleKeyDown = (e) => {
      if ((e.metaKey || e.ctrlKey) && e.key === 'z' && !e.shiftKey) {
        e.preventDefault();
        performUndo();
      }
      if ((e.metaKey || e.ctrlKey) && ((e.key === 'z' && e.shiftKey) || e.key === 'y')) {
        e.preventDefault();
        performRedo();
      }
    };
    
    window.addEventListener('keydown', handleKeyDown);

    return () => {
      window.removeEventListener('keydown', handleKeyDown);
    };
  }, [performUndo, performRedo]);
  
  // Track state changes for undo history (debounced)
  const saveHistoryTimeoutRef = useRef(null);
  useEffect(() => {
    if (saveHistoryTimeoutRef.current) {
      clearTimeout(saveHistoryTimeoutRef.current);
    }
    
    saveHistoryTimeoutRef.current = setTimeout(() => {
      if (shapes.length > 0 || Object.keys(shapeSettings).length > 0) {
        saveToHistory();
      }
    }, 500);
    
    return () => {
      if (saveHistoryTimeoutRef.current) {
        clearTimeout(saveHistoryTimeoutRef.current);
      }
    };
  }, [shapes, shapeSettings, screens, canvasWidth, canvasHeight, innerMargin]);
  
  // Persist UI layout state to localStorage
  useEffect(() => {
    try {
      localStorage.setItem('resolume-collapsed-sections', JSON.stringify(collapsedSections));
    } catch (e) {}
  }, [collapsedSections]);
  
  useEffect(() => {
    try {
      localStorage.setItem('resolume-section-order', JSON.stringify(sectionOrder));
    } catch (e) {}
  }, [sectionOrder]);
  
  useEffect(() => {
    try {
      localStorage.setItem('resolume-section-columns', JSON.stringify(sectionColumns));
    } catch (e) {}
  }, [sectionColumns]);
  
  useEffect(() => {
    try {
      localStorage.setItem('resolume-side-by-side', JSON.stringify(sideBySidePreview));
    } catch (e) {}
  }, [sideBySidePreview]);
  
  useEffect(() => {
    try {
      localStorage.setItem('resolume-preview-span', JSON.stringify(previewSpanColumns));
    } catch (e) {}
  }, [previewSpanColumns]);
  
  useEffect(() => {
    try {
      if (savedLayout) {
        localStorage.setItem('resolume-saved-layout', JSON.stringify(savedLayout));
      }
    } catch (e) {}
  }, [savedLayout, defaultSectionOrder, defaultSectionColumns, sideBySidePreview, previewSpanColumns]);
  
  useEffect(() => {
    try {
      localStorage.setItem('resolume-use-artboard', JSON.stringify(useArtboard));
    } catch (e) {}
  }, [useArtboard]);

  // Section collapse/expand toggle
  const toggleSection = useCallback((sectionId) => {
    setCollapsedSections(prev => ({
      ...prev,
      [sectionId]: !prev[sectionId]
    }));
  }, []);
  
  // Move section to other column
  const moveToColumn = useCallback((sectionId, column) => {
    setSectionColumns(prev => ({
      ...prev,
      [sectionId]: column
    }));
  }, []);
  
  // Drag and drop handlers for section reordering
  const handleDragStart = useCallback((e, sectionId) => {
    // Prevent dragging when interacting with form elements
    const target = e.target;
    const tagName = target.tagName.toLowerCase();
    if (tagName === 'input' || tagName === 'textarea' || tagName === 'select' || tagName === 'button') {
      e.preventDefault();
      return;
    }
    // Also check if we're inside a form element
    if (target.closest('input, textarea, select, button')) {
      e.preventDefault();
      return;
    }
    
    setDraggedSection(sectionId);
    e.dataTransfer.effectAllowed = 'move';
    e.dataTransfer.setData('text/plain', sectionId);
  }, []);
  
  const handleDragOver = useCallback((e, targetSectionId, targetColumn) => {
    e.preventDefault();
    if (!draggedSection || draggedSection === targetSectionId) return;
    
    // Update column if dragging to different column
    if (targetColumn && sectionColumns[draggedSection] !== targetColumn) {
      setSectionColumns(prev => ({
        ...prev,
        [draggedSection]: targetColumn
      }));
    }
    
    // Reorder within sections
    setSectionOrder(prev => {
      const newOrder = [...prev];
      const draggedIdx = newOrder.indexOf(draggedSection);
      const targetIdx = newOrder.indexOf(targetSectionId);
      
      if (draggedIdx === -1 || targetIdx === -1) return prev;
      
      newOrder.splice(draggedIdx, 1);
      newOrder.splice(targetIdx, 0, draggedSection);
      return newOrder;
    });
  }, [draggedSection, sectionColumns]);
  
  // Handle drop on empty column area
  const handleColumnDrop = useCallback((e, column) => {
    e.preventDefault();
    if (!draggedSection) return;
    
    setSectionColumns(prev => ({
      ...prev,
      [draggedSection]: column
    }));
    setDraggedSection(null);
  }, [draggedSection]);
  
  const handleDragEnd = useCallback(() => {
    setDraggedSection(null);
  }, []);
  
  // Screen management
  const addScreen = useCallback(() => {
    const newId = Math.max(...screens.map(s => s.id), 0) + 1;
    setScreens(prev => [...prev, { id: newId, name: `Screen ${newId}`, width: canvasWidth, height: canvasHeight }]);
  }, [screens, canvasWidth, canvasHeight]);
  
  const removeScreen = useCallback((screenId) => {
    if (screens.length <= 1) return;
    setScreens(prev => prev.filter(s => s.id !== screenId));
    const firstScreenId = screens.find(s => s.id !== screenId)?.id || 1;
    setShapeSettings(prev => {
      const newSettings = { ...prev };
      Object.keys(newSettings).forEach(key => {
        if (newSettings[key].screen === screenId) {
          newSettings[key] = { ...newSettings[key], screen: firstScreenId };
        }
      });
      return newSettings;
    });
  }, [screens]);
  
  const renameScreen = useCallback((screenId, newName) => {
    setScreens(prev => prev.map(s => 
      s.id === screenId ? { ...s, name: newName } : s
    ));
  }, []);
  
  const updateScreenSize = useCallback((screenId, width, height) => {
    setScreens(prev => prev.map(s => 
      s.id === screenId ? { ...s, width, height } : s
    ));
  }, []);
  
  const applyCanvasSizeToScreen = useCallback((screenId) => {
    setScreens(prev => prev.map(s => 
      s.id === screenId ? { ...s, width: canvasWidth, height: canvasHeight } : s
    ));
  }, [canvasWidth, canvasHeight]);
  
  const applyCanvasSizeToAllScreens = useCallback(() => {
    setScreens(prev => prev.map(s => ({ ...s, width: canvasWidth, height: canvasHeight })));
  }, [canvasWidth, canvasHeight]);
  
  // Initialize settings for a shape based on default output type
  const getDefaultSettings = useCallback((outputType) => ({
    enabled: true,
    slice: outputType === 'slice' || outputType === 'both',
    mask: outputType === 'mask' || outputType === 'both',
    screen: 1,
    customName: '',
    invertMask: true,
    bezierMode: false
  }), []);
  
  // Update shape setting
  const updateShapeSetting = useCallback((index, field, value) => {
    setShapeSettings(prev => ({
      ...prev,
      [index]: {
        ...prev[index],
        [field]: value
      }
    }));
  }, []);
  
  // Update a single point in a shape
  const updateShapePoint = useCallback((shapeIndex, pointIndex, newX, newY) => {
    setShapes(prev => {
      const newShapes = [...prev];
      const shape = { ...newShapes[shapeIndex] };
      const newPoints = [...shape.points];
      newPoints[pointIndex] = { x: newX, y: newY };
      shape.points = newPoints;
      
      // Recalculate bounding box
      const xs = newPoints.map(p => p.x);
      const ys = newPoints.map(p => p.y);
      shape.bbox = {
        minX: Math.min(...xs),
        maxX: Math.max(...xs),
        minY: Math.min(...ys),
        maxY: Math.max(...ys)
      };
      
      newShapes[shapeIndex] = shape;
      return newShapes;
    });
  }, []);
  
  // Clear editing point when clicking elsewhere
  const clearEditingPoint = useCallback(() => {
    if (!isDraggingPoint) {
      setEditingPoint(null);
    }
  }, [isDraggingPoint]);

  // Keep at least one selection filter active so the preview never becomes empty unintentionally
  const toggleSelectionFilter = useCallback((key) => {
    setSelectionFilter(prev => {
      const next = { ...prev, [key]: !prev[key] };
      if (!next.slice && !next.mask && !next.flagged) {
        return prev;
      }
      return next;
    });
  }, []);
  
  // Set all shapes to a specific output type
  const setAllShapesTo = useCallback((type) => {
    const newSettings = {};
    shapes.forEach((_, i) => {
      newSettings[i] = {
        enabled: shapeSettings[i]?.enabled ?? true,
        slice: type === 'slice' || type === 'both',
        mask: type === 'mask' || type === 'both',
        screen: shapeSettings[i]?.screen ?? 1,
        customName: shapeSettings[i]?.customName ?? '',
        invertMask: shapeSettings[i]?.invertMask ?? true,
        bezierMode: shapeSettings[i]?.bezierMode ?? false
      };
    });
    setShapeSettings(newSettings);
  }, [shapes, shapeSettings]);
  
  // Toggle all shapes enabled/disabled
  const toggleAllShapes = useCallback((enabled) => {
    const newSettings = {};
    shapes.forEach((_, i) => {
      newSettings[i] = {
        ...shapeSettings[i],
        enabled
      };
    });
    setShapeSettings(newSettings);
  }, [shapes, shapeSettings]);
  
  // Apply default output type to all shapes
  const applyDefaultToAll = useCallback(() => {
    setAllShapesTo(defaultOutputType);
  }, [setAllShapesTo, defaultOutputType]);
  
  // Toggle all shapes enabled/disabled
  const toggleAllEnabled = useCallback(() => {
    const allEnabled = shapes.every((_, i) => shapeSettings[i]?.enabled);
    toggleAllShapes(!allEnabled);
  }, [shapes, shapeSettings, toggleAllShapes]);
  
  // Assign all shapes to a specific screen
  const assignAllToScreen = useCallback((screenId) => {
    const newSettings = {};
    shapes.forEach((_, i) => {
      newSettings[i] = {
        ...shapeSettings[i],
        screen: screenId
      };
    });
    setShapeSettings(newSettings);
  }, [shapes, shapeSettings]);

  // Convert DXF directly to shapes using polylines to avoid SVG parsing issues
  const extractShapesFromDxf = useCallback((dxfText, canvasWidth, canvasHeight, innerMargin, scaleToFit) => {
    if (!window.dxf?.parseString || !window.dxf?.toPolylines) return null;
    try {
      const parsed = window.dxf.parseString(dxfText);
      const { bbox, polylines } = window.dxf.toPolylines(parsed);
      if (!polylines || polylines.length === 0) return [];

      const availableWidth = canvasWidth - innerMargin * 2;
      const availableHeight = canvasHeight - innerMargin * 2;
      const contentWidth = bbox.max.x - bbox.min.x;
      const contentHeight = bbox.max.y - bbox.min.y;

      let scale = 1;
      let offsetX = innerMargin;
      let offsetY = innerMargin;

      if (scaleToFit && contentWidth > 0 && contentHeight > 0) {
        const scaleX = availableWidth / contentWidth;
        const scaleY = availableHeight / contentHeight;
        scale = Math.min(scaleX, scaleY);
        offsetX = innerMargin + (availableWidth - contentWidth * scale) / 2 - bbox.min.x * scale;
        offsetY = innerMargin + (availableHeight - contentHeight * scale) / 2 - bbox.min.y * scale;
      }

      return polylines.map((pl, idx) => {
        const layerName = pl.layer || pl.LAYER || pl.layerName || null;
        const scaledPoints = pl.vertices.map(([x, y]) => ({
          x: x * scale + offsetX,
          y: (bbox.max.y - (y - bbox.min.y)) * scale + (innerMargin + (availableHeight - contentHeight * scale) / 2)
        }));
        const xs = scaledPoints.map(p => p.x);
        const ys = scaledPoints.map(p => p.y);
        return {
          name: `DXF_Polyline_${idx + 1}`,
          points: scaledPoints,
          bezierData: null,
          hasBezierCurves: false,
          sourceType: 'dxf-polyline',
          layer: layerName,
          bbox: {
            minX: Math.min(...xs),
            maxX: Math.max(...xs),
            minY: Math.min(...ys),
            maxY: Math.max(...ys)
          }
        };
      });
    } catch (err) {
      console.error('DXF polyline extraction failed', err);
      return null;
    }
  }, []);

  // Normalize DXF-generated SVG so coordinates start at (0,0) and Y grows downward
  const normalizeDxfSvg = useCallback((dxfSvgText) => {
    try {
      const parser = new DOMParser();
      const doc = parser.parseFromString(dxfSvgText, 'image/svg+xml');
      const svg = doc.querySelector('svg');
      if (!svg) return dxfSvgText;
      
      const vb = (svg.getAttribute('viewBox') || '').trim().split(/\\s+/).map(Number);
      if (vb.length < 4 || vb.some(v => Number.isNaN(v))) return dxfSvgText;
      const [minX, minY, width, height] = vb;
      
      // Desired transform: translate(-minX, -minY) then flip Y
      const tx = -minX;
      const ty = -minY;
      const newTransform = `matrix(1 0 0 -1 ${tx} ${ty})`;
      
      // Apply to first <g> with a transform or wrap contents
      const target = svg.querySelector('g[transform]') || svg.firstElementChild;
      if (target) {
        target.setAttribute('transform', newTransform);
      } else {
        const g = doc.createElementNS(svg.namespaceURI, 'g');
        g.setAttribute('transform', newTransform);
        while (svg.firstChild) g.appendChild(svg.firstChild);
        svg.appendChild(g);
      }
      
      // Reset viewBox to start at 0,0
      svg.setAttribute('viewBox', `0 0 ${width} ${height}`);
      const serialized = new XMLSerializer().serializeToString(doc);
      return serialized;
    } catch (err) {
      console.warn('DXF normalization failed; using raw SVG', err);
      return dxfSvgText;
    }
  }, []);
  
  const presets = [
    { name: '4K UHD', width: 3840, height: 2160 },
    { name: '1080p', width: 1920, height: 1080 },
    { name: '720p', width: 1280, height: 720 },
    { name: '4K DCI', width: 4096, height: 2160 },
    { name: 'Square 1080', width: 1080, height: 1080 },
    { name: 'Square 2160', width: 2160, height: 2160 },
  ];
  
  const handleFileUpload = useCallback(async (e) => {
    let svgContent;
    let fileNameRaw;
    let file;
    let isDxf = false;
    let dxfText = null;
    
    // Handle custom event from menu
    if (e?.detail?.content) {
      svgContent = e.detail.content;
      fileNameRaw = e.detail.fileName || 'untitled';
    } else if (e?.target?.files?.[0]) {
      // Browser: use file input
      file = e.target.files[0];
      fileNameRaw = file.name;
      const lowerName = file.name.toLowerCase();
      const isSvgz = lowerName.endsWith('.svgz');
      
      if (isSvgz) {
        try {
          const compressed = await file.arrayBuffer();
          const ds = new DecompressionStream('gzip');
          const decompressedStream = new Response(compressed).body.pipeThrough(ds);
          const decompressedBuffer = await new Response(decompressedStream).arrayBuffer();
          svgContent = new TextDecoder().decode(decompressedBuffer);
        } catch (err) {
          console.error('Error decompressing SVGZ:', err);
          alert('Error decompressing SVGZ file. The file may be corrupted.');
          return;
        }
      } else {
        svgContent = await file.text();
      }
    } else {
      return;
    }
    
    const lowerName = (fileNameRaw || '').toLowerCase();
    isDxf = lowerName.endsWith('.dxf');
    const baseName = (fileNameRaw || 'untitled').replace(/\.(svg|svgz|dxf)$/i, '');
    
    if (isDxf) {
      if (!window.dxf?.Helper) {
        alert('DXF support failed to load. Check your connection and reload the page.');
        return;
      }
      try {
      dxfText = svgContent;
      const helper = new window.dxf.Helper(dxfText);
      svgContent = normalizeDxfSvg(helper.toSVG());
      // Ensure DXF fits the canvas by default
      setScaleToFit(true);
      setUseArtboard(false);
    } catch (err) {
      console.error('Error parsing DXF:', err);
        alert('Error parsing DXF file. The file may be corrupted or unsupported.');
        return;
      }
    }
    
    setFileName(baseName);
    setSvgText(svgContent);
    
    // Extract document title from XMP metadata or SVG title element
    const docTitle = getDocumentTitle(svgContent);
    setDocumentTitle(docTitle || '');
    
    // Set project name based on nameSource preference
    if (nameSource === 'title' && docTitle) {
      setProjectName(docTitle);
    } else {
      setProjectName(baseName);
    }
    
    // Extract artboard size and set canvas dimensions if useArtboard is enabled
    let newCanvasWidth = canvasWidth;
    let newCanvasHeight = canvasHeight;
    if (useArtboard) {
      const artboard = getArtboardSize(svgContent);
      if (artboard) {
        newCanvasWidth = artboard.width;
        newCanvasHeight = artboard.height;
        setCanvasWidth(artboard.width);
        setCanvasHeight(artboard.height);
        // Update first screen to match
        setScreens(prev => {
          if (prev.length === 1) {
            return [{ ...prev[0], width: artboard.width, height: artboard.height }];
          }
          return prev;
        });
      }
    }
    
    const effectiveScaleToFit = isDxf ? true : scaleToFit;
    let extractedShapes;
    if (isDxf) {
      extractedShapes = extractShapesFromDxf(dxfText || svgContent, newCanvasWidth, newCanvasHeight, innerMargin, true) || [];
      // Fallback to SVG extraction if DXF polyline path yields nothing
      if (!extractedShapes || extractedShapes.length === 0) {
        extractedShapes = extractShapesFromSVG(svgContent, newCanvasWidth, newCanvasHeight, bezierResolution, innerMargin, true, false, shapeNameMode, false, skipStrokeOnly);
      }
    } else {
      extractedShapes = extractShapesFromSVG(svgContent, newCanvasWidth, newCanvasHeight, bezierResolution, innerMargin, effectiveScaleToFit, false, shapeNameMode, false, skipStrokeOnly);
    }
    setShapes(extractedShapes);
    
    // Initialize settings for each shape
    const initialSettings = {};
    extractedShapes.forEach((_, i) => {
      initialSettings[i] = {
        enabled: true,
        slice: defaultOutputType === 'slice' || defaultOutputType === 'both',
        mask: defaultOutputType === 'mask' || defaultOutputType === 'both',
        screen: 1
      };
    });
    setShapeSettings(initialSettings);
    setLastSelectedShape(null);
    setPreviewSelectedShape(null);
    setPreviewZoom(1);
    setPreviewPan({ x: 0, y: 0 });
    setAutoCloseOpenPaths(false);
    setExtractClipPaths(false);
    setSkipStrokeOnly(false);
  }, [canvasWidth, canvasHeight, bezierResolution, innerMargin, scaleToFit, defaultOutputType, shapeNameMode, useArtboard, nameSource, normalizeDxfSvg]);
  
  // Handler for switching between Title and Filename naming modes
  const handleNameSourceChange = useCallback((source) => {
    setNameSource(source);
    if (source === 'title' && documentTitle) {
      setProjectName(documentTitle);
    } else if (source === 'filename' && fileName) {
      setProjectName(fileName);
    } else if (source === 'custom') {
      setProjectName(customProjectName);
    }
  }, [documentTitle, fileName, customProjectName]);
  
  // Handler for when user types in the Project Name field
  const handleProjectNameInput = useCallback((value) => {
    setProjectName(value);
    setCustomProjectName(value);
    setNameSource('custom');
  }, []);
  
  const handleCanvasChange = useCallback((width, height) => {
    setCanvasWidth(width);
    setCanvasHeight(height);
    
    // Update first screen to match canvas size (or all screens if only one)
    setScreens(prev => {
      if (prev.length === 1) {
        return [{ ...prev[0], width, height }];
      }
      return prev;
    });
    
    if (svgText) {
      const extractedShapes = extractShapesFromSVG(svgText, width, height, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, autoCloseOpenPaths, skipStrokeOnly);
      setShapes(extractedShapes);
    }
  }, [svgText, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode]);
  
  const handleInnerMarginChange = useCallback((margin) => {
    setInnerMargin(margin);
    
    if (svgText) {
      const extractedShapes = extractShapesFromSVG(svgText, canvasWidth, canvasHeight, bezierResolution, margin, scaleToFit, extractClipPaths, shapeNameMode, autoCloseOpenPaths, skipStrokeOnly);
      setShapes(extractedShapes);
    }
  }, [svgText, canvasWidth, canvasHeight, bezierResolution, scaleToFit, extractClipPaths, shapeNameMode]);
  
  const handleScaleToFitChange = useCallback((enabled) => {
    setScaleToFit(enabled);
    
    if (svgText) {
      const extractedShapes = extractShapesFromSVG(svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin, enabled, extractClipPaths, shapeNameMode, autoCloseOpenPaths, skipStrokeOnly);
      setShapes(extractedShapes);
    }
  }, [svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin, extractClipPaths, shapeNameMode]);
  
  const handleExtractClipPathsChange = useCallback((enabled) => {
    setExtractClipPaths(enabled);
    
    if (svgText) {
      const extractedShapes = extractShapesFromSVG(svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin, scaleToFit, enabled, shapeNameMode, autoCloseOpenPaths, skipStrokeOnly);
      setShapes(extractedShapes);
      
      // Initialize settings for new shapes
      const initialSettings = {};
      extractedShapes.forEach((_, i) => {
        initialSettings[i] = shapeSettings[i] || {
          enabled: true,
          slice: defaultOutputType === 'slice' || defaultOutputType === 'both',
          mask: defaultOutputType === 'mask' || defaultOutputType === 'both',
          screen: 1
        };
      });
      setShapeSettings(initialSettings);
    }
  }, [svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin, scaleToFit, shapeSettings, defaultOutputType, shapeNameMode, autoCloseOpenPaths]);
  
  const handleAutoCloseOpenPathsChange = useCallback((enabled) => {
    setAutoCloseOpenPaths(enabled);
    
    if (svgText) {
      const extractedShapes = extractShapesFromSVG(svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, enabled, skipStrokeOnly);
      setShapes(extractedShapes);
    }
  }, [svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, skipStrokeOnly]);
  
  const handleSkipStrokeOnlyChange = useCallback((enabled) => {
    setSkipStrokeOnly(enabled);
    
    if (svgText) {
      const extractedShapes = extractShapesFromSVG(svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, autoCloseOpenPaths, enabled);
      setShapes(extractedShapes);
      
      // Initialize settings for new shapes
      const initialSettings = {};
      extractedShapes.forEach((_, i) => {
        initialSettings[i] = shapeSettings[i] || {
          enabled: true,
          slice: defaultOutputType === 'slice' || defaultOutputType === 'both',
          mask: defaultOutputType === 'mask' || defaultOutputType === 'both',
          screen: 1
        };
      });
      setShapeSettings(initialSettings);
    }
  }, [svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, autoCloseOpenPaths, shapeSettings, defaultOutputType]);
  
  // Compute if there are any shapes with issues, and if any are enabled
  const shapesWithIssuesInfo = useMemo(() => {
    let hasIssues = false;
    let hasEnabledIssues = false;
    const issueIndices = [];
    
    shapes.forEach((shape, i) => {
      const isOpen = isShapeOpen(shape.points, shape.bbox, shape.sourceType);
      const isSelfIntersecting = hasSelfIntersection(shape.points, shape.sourceType, shape.isCompoundSubpath);
      const hasIssue = isOpen || isSelfIntersecting;
      const layerEnabled = isLayerEnabled(shape.layer);
      
      if (hasIssue) {
        hasIssues = true;
        issueIndices.push(i);
        const settings = shapeSettings[i] || { enabled: true };
        if (settings.enabled && layerEnabled) {
          hasEnabledIssues = true;
        }
      }
    });
    
    return { hasIssues, hasEnabledIssues, issueIndices };
  }, [shapes, shapeSettings]);
  
  const handleToggleShapesWithIssues = useCallback(() => {
    if (shapes.length === 0) return;
    
    const { hasEnabledIssues, issueIndices } = shapesWithIssuesInfo;
    const newSettings = { ...shapeSettings };
    
    // Toggle: if any are enabled, disable all; if all disabled, enable all
    const newEnabledState = !hasEnabledIssues;
    
    issueIndices.forEach(i => {
      newSettings[i] = {
        ...newSettings[i],
        enabled: newEnabledState
      };
    });
    
    setShapeSettings(newSettings);
  }, [shapes, shapeSettings, shapesWithIssuesInfo]);
  
  const handleBezierResolutionChange = useCallback((resolution) => {
    setBezierResolution(resolution);
    
    if (svgText) {
      const extractedShapes = extractShapesFromSVG(svgText, canvasWidth, canvasHeight, resolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, autoCloseOpenPaths, skipStrokeOnly);
      setShapes(extractedShapes);
    }
  }, [svgText, canvasWidth, canvasHeight, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, skipStrokeOnly]);
  
  const handleUseArtboardChange = useCallback((enabled) => {
    setUseArtboard(enabled);
    
    if (svgText) {
      if (enabled) {
        // If enabling, apply artboard size immediately
        const artboard = getArtboardSize(svgText);
        if (artboard) {
          setCanvasWidth(artboard.width);
          setCanvasHeight(artboard.height);
          // Update first screen to match
          setScreens(prev => {
            if (prev.length === 1) {
              return [{ ...prev[0], width: artboard.width, height: artboard.height }];
            }
            return prev;
          });
          // Re-extract shapes with artboard size
          const extractedShapes = extractShapesFromSVG(svgText, artboard.width, artboard.height, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, autoCloseOpenPaths, skipStrokeOnly);
          setShapes(extractedShapes);
        }
      } else {
        // If disabling artboard mode, revert to default canvas size and re-extract
        const newWidth = defaultCanvasSize.width;
        const newHeight = defaultCanvasSize.height;
        setCanvasWidth(newWidth);
        setCanvasHeight(newHeight);
        // Update first screen to match
        setScreens(prev => {
          if (prev.length === 1) {
            return [{ ...prev[0], width: newWidth, height: newHeight }];
          }
          return prev;
        });
        // Re-extract shapes with default canvas size
        const extractedShapes = extractShapesFromSVG(svgText, newWidth, newHeight, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, autoCloseOpenPaths, skipStrokeOnly);
        setShapes(extractedShapes);
      }
    }
  }, [svgText, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, defaultCanvasSize, autoCloseOpenPaths]);
  
  // Apply artboard size without toggling the setting
  const applyArtboardSize = useCallback(() => {
    if (svgText) {
      const artboard = getArtboardSize(svgText);
      if (artboard) {
        setCanvasWidth(artboard.width);
        setCanvasHeight(artboard.height);
        // Update first screen to match
        setScreens(prev => {
          if (prev.length === 1) {
            return [{ ...prev[0], width: artboard.width, height: artboard.height }];
          }
          return prev;
        });
        // Re-extract shapes with new canvas size
        const extractedShapes = extractShapesFromSVG(svgText, artboard.width, artboard.height, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, autoCloseOpenPaths, skipStrokeOnly);
        setShapes(extractedShapes);
      }
    }
  }, [svgText, bezierResolution, innerMargin, scaleToFit, extractClipPaths, shapeNameMode]);
  
  const toggleShapeNameOption = useCallback((option) => {
    setShapeNameMode(prev => {
      const newMode = { ...prev, [option]: !prev[option] };
      
      if (svgText) {
        const extractedShapes = extractShapesFromSVG(svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin, scaleToFit, extractClipPaths, newMode, autoCloseOpenPaths, skipStrokeOnly);
        setShapes(extractedShapes);
      }
      
      return newMode;
    });
  }, [svgText, canvasWidth, canvasHeight, bezierResolution, innerMargin, scaleToFit, extractClipPaths, autoCloseOpenPaths, skipStrokeOnly]);
  
  const downloadXml = useCallback(async () => {
    if (shapes.length === 0) return;
    
    // Check if any masks are actually selected
    const hasMasks = shapes.some((shape, i) => shapeSettings[i]?.enabled && isLayerEnabled(shape.layer) && shapeSettings[i]?.mask);
    
    // Uncheck combine masks if no masks selected
    if (combineMasks && !hasMasks) {
      setCombineMasks(false);
    }
    
    const exportName = projectName || fileName || 'Converted_SVG';
    const xml = generateResolumeXML(shapes, shapeSettings, screens, exportName, canvasWidth, canvasHeight, combineMasks && hasMasks, layerVisibility);
    const suggestedName = `${exportName}.xml`;
    
    const blob = new Blob([xml], { type: 'application/xml' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = suggestedName;
    a.style.display = 'none';
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  }, [shapes, shapeSettings, screens, projectName, fileName, canvasWidth, canvasHeight, combineMasks, layerVisibility, isLayerEnabled]);
  
  // Save project to file
  const saveProject = useCallback(async () => {
    const project = {
      version: 1,
      projectName: projectName || fileName || 'Untitled',
      svgText,
      fileName,
      canvasWidth,
      canvasHeight,
      innerMargin,
      scaleToFit,
      extractClipPaths,
      shapeNameMode,
      bezierResolution,
      defaultOutputType,
      combineMasks,
      screens,
      shapeSettings,
      layerVisibility
    };
    
    const json = JSON.stringify(project, null, 2);
    const suggestedName = `${projectName || fileName || 'Untitled'}.rslm`;
    
    const blob = new Blob([json], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = suggestedName;
    a.style.display = 'none';
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  }, [projectName, svgText, fileName, canvasWidth, canvasHeight, innerMargin, scaleToFit, extractClipPaths, shapeNameMode, bezierResolution, defaultOutputType, combineMasks, screens, shapeSettings, layerVisibility]);
  
  // Load project from file
  const loadProject = useCallback(async (e) => {
    let projectData;
    
    // Handle custom event from menu
    if (e?.detail?.content) {
      projectData = e.detail.content;
    } else if (e?.target?.files?.[0]) {
      // Browser: use file input
      const file = e.target.files[0];
      projectData = await new Promise((resolve, reject) => {
        const reader = new FileReader();
        reader.onload = (event) => resolve(event.target.result);
        reader.onerror = reject;
        reader.readAsText(file);
      });
      e.target.value = '';
    } else {
      return;
    }
    
    try {
      const project = JSON.parse(projectData);
      
      // Restore state from project
      if (project.svgText) setSvgText(project.svgText);
      if (project.fileName) setFileName(project.fileName);
      if (project.projectName) setProjectName(project.projectName);
      if (project.canvasWidth) setCanvasWidth(project.canvasWidth);
      if (project.canvasHeight) setCanvasHeight(project.canvasHeight);
      if (typeof project.innerMargin === 'number') setInnerMargin(project.innerMargin);
      if (typeof project.scaleToFit === 'boolean') setScaleToFit(project.scaleToFit);
      if (typeof project.extractClipPaths === 'boolean') setExtractClipPaths(project.extractClipPaths);
      if (project.bezierResolution) setBezierResolution(project.bezierResolution);
      if (project.defaultOutputType) setDefaultOutputType(project.defaultOutputType);
      if (typeof project.combineMasks === 'boolean') setCombineMasks(project.combineMasks);
      if (project.screens) setScreens(project.screens);
      if (project.shapeSettings) setShapeSettings(project.shapeSettings);
      if (project.shapeNameMode) setShapeNameMode(project.shapeNameMode);
      if (project.layerVisibility) setLayerVisibility(project.layerVisibility);
      
      // Re-extract shapes from SVG with saved settings
      if (project.svgText) {
        const extractedShapes = extractShapesFromSVG(
          project.svgText, 
          project.canvasWidth || 3840, 
          project.canvasHeight || 2160, 
          project.bezierResolution || 10,
          project.innerMargin || 0,
          project.scaleToFit !== false,
          project.extractClipPaths || false,
          project.shapeNameMode || 'type',
          project.autoCloseOpenPaths || false,
          project.skipStrokeOnly || false
        );
        setShapes(extractedShapes);
      }
    } catch (err) {
      alert('Error loading project file. Please ensure it is a valid .rslm file.');
      console.error('Project load error:', err);
    }
  }, []);
  
  // New project - reset everything
  const newProject = () => {
    setSvgText('');
    setFileName('');
    setProjectName('');
    setShapes([]);
    setShapeSettings({});
    setLayerVisibility({});
    setCanvasWidth(defaultCanvasSize.width);
    setCanvasHeight(defaultCanvasSize.height);
    setInnerMargin(0);
    setScaleToFit(true);
    setExtractClipPaths(false);
    setAutoCloseOpenPaths(false);
    setSkipStrokeOnly(false);
    setBezierResolution(10);
    setDefaultOutputType('slice');
    setScreens([{ id: 1, name: 'Screen 1', width: defaultCanvasSize.width, height: defaultCanvasSize.height }]);
    setCombineMasks(false);
    // Reset preview viewport
    setPreviewZoom(1);
    setPreviewPan({ x: 0, y: 0 });
    setIsTrackingEnabled(false);
    setLastSelectedShape(null);
    setPreviewSelectedShape(null);
    // Reset file inputs
    if (fileInputRef.current) fileInputRef.current.value = '';
    if (projectInputRef.current) projectInputRef.current.value = '';
  };
  
  
  // Preview dimensions (defined early for use in callbacks)
  const previewAspect = canvasWidth / canvasHeight;
  const previewWidth = 500;
  const previewHeight = previewWidth / previewAspect;
  const scale = previewWidth / canvasWidth;
  
  // Refs for wheel handler to avoid stale closures
  const zoomRef = useRef(previewZoom);
  const panRef = useRef(previewPan);
  zoomRef.current = previewZoom;
  panRef.current = previewPan;
  
  // Store wheel handler ref to remove listener on cleanup
  const wheelHandlerRef = useRef(null);
  
  // Preview viewport wheel zoom handler
  const handlePreviewWheel = useCallback((e) => {
    e.preventDefault();
    e.stopPropagation();
    
    const zoomFactor = e.deltaY > 0 ? 0.9 : 1.1;
    
    // Get mouse position relative to the preview container
    const rect = e.currentTarget?.getBoundingClientRect();
    if (!rect) return;
    
    // Mouse position in DOM pixels
    const domMouseX = e.clientX - rect.left;
    const domMouseY = e.clientY - rect.top;
    
    // Convert DOM coordinates to SVG viewBox coordinates
    // This accounts for when the SVG is rendered at a different size than its viewBox
    const scaleX = previewWidth / rect.width;
    const scaleY = previewHeight / rect.height;
    const mouseX = domMouseX * scaleX;
    const mouseY = domMouseY * scaleY;
    
    const currentZoom = zoomRef.current;
    const currentPan = panRef.current;
    
    // Calculate the content point under the mouse before zoom
    const contentX = (mouseX - currentPan.x) / currentZoom;
    const contentY = (mouseY - currentPan.y) / currentZoom;
    
    // Calculate new zoom
    const newZoom = Math.min(Math.max(currentZoom * zoomFactor, 0.1), 10);
    
    // Calculate new pan so the same content point stays under the mouse
    const newPanX = mouseX - contentX * newZoom;
    const newPanY = mouseY - contentY * newZoom;
    
    setPreviewZoom(newZoom);
    setPreviewPan({ x: newPanX, y: newPanY });
  }, [previewWidth, previewHeight]);
  
  // Ref callback to attach wheel listener with passive: false
  const previewContainerRefCallback = useCallback((node) => {
    // Remove listener from previous node
    if (previewContainerRef.current && wheelHandlerRef.current) {
      previewContainerRef.current.removeEventListener('wheel', wheelHandlerRef.current);
    }
    
    // Store the new node
    previewContainerRef.current = node;
    
    // Attach listener to new node
    if (node) {
      wheelHandlerRef.current = handlePreviewWheel;
      node.addEventListener('wheel', handlePreviewWheel, { passive: false });
    }
  }, [handlePreviewWheel]);
  
  // Refs for drag handling to avoid stale closures
  const isDraggingPointRef = useRef(isDraggingPoint);
  const editingPointRef = useRef(editingPoint);
  const isPanningRef = useRef(isPanning);
  const panStartRef = useRef(panStart);
  const dragOffsetRef = useRef(dragOffset);
  isDraggingPointRef.current = isDraggingPoint;
  editingPointRef.current = editingPoint;
  isPanningRef.current = isPanning;
  panStartRef.current = panStart;
  dragOffsetRef.current = dragOffset;
  
  const handlePreviewMouseDown = useCallback((e) => {
    if (e.button === 0 && !isDraggingPointRef.current) { // Left mouse button, not dragging a point
      setIsPanning(true);
      // Store initial mouse position and pan in screen coordinates
      setPanStart({ 
        mouseX: e.clientX, 
        mouseY: e.clientY,
        panX: panRef.current.x,
        panY: panRef.current.y
      });
    }
  }, []);
  
  const handlePreviewMouseMove = useCallback((e) => {
    if (isDraggingPointRef.current && editingPointRef.current && previewContainerRef.current) {
      // Handle point dragging
      const rect = previewContainerRef.current.getBoundingClientRect();
      const mouseX = e.clientX - rect.left;
      const mouseY = e.clientY - rect.top;
      
      // Account for potential viewBox scaling (when container size differs from previewWidth/Height)
      const scaleX = previewWidth / rect.width;
      const scaleY = previewHeight / rect.height;
      
      // Convert DOM coordinates to SVG viewBox coordinates
      const svgMouseX = mouseX * scaleX;
      const svgMouseY = mouseY * scaleY;
      
      // Convert to canvas coordinates, accounting for drag offset
      const currentPan = panRef.current;
      const currentZoom = zoomRef.current;
      const offset = dragOffsetRef.current;
      
      // Apply offset so point doesn't jump to cursor
      const canvasX = (svgMouseX - currentPan.x - offset.x) / currentZoom / scale;
      const canvasY = (svgMouseY - currentPan.y - offset.y) / currentZoom / scale;
      
      updateShapePoint(editingPointRef.current.shapeIndex, editingPointRef.current.pointIndex, canvasX, canvasY);
    } else if (isPanningRef.current && previewContainerRef.current) {
      // Get scale factors for viewBox
      const rect = previewContainerRef.current.getBoundingClientRect();
      const scaleX = previewWidth / rect.width;
      const scaleY = previewHeight / rect.height;
      
      // Calculate mouse delta in screen coordinates, then convert to viewBox coordinates
      const start = panStartRef.current;
      const deltaX = (e.clientX - start.mouseX) * scaleX;
      const deltaY = (e.clientY - start.mouseY) * scaleY;
      
      setPreviewPan({
        x: start.panX + deltaX,
        y: start.panY + deltaY
      });
    }
  }, [scale, updateShapePoint, previewWidth, previewHeight]);
  
  const handlePreviewMouseUp = useCallback(() => {
    setIsPanning(false);
    if (isDraggingPointRef.current) {
      setIsDraggingPoint(false);
    }
  }, []);
  
  const handlePreviewMouseLeave = useCallback(() => {
    setIsPanning(false);
    if (isDraggingPointRef.current) {
      setIsDraggingPoint(false);
    }
  }, []);
  
  const zoomIn = useCallback(() => {
    const zoomFactor = 1.2;
    const newZoom = Math.min(previewZoom * zoomFactor, 10);
    
    // Zoom centered on viewport center
    const centerX = previewWidth / 2;
    const centerY = previewHeight / 2;
    
    // Content point at viewport center
    const contentX = (centerX - previewPan.x) / previewZoom;
    const contentY = (centerY - previewPan.y) / previewZoom;
    
    // New pan to keep center point centered
    const newPanX = centerX - contentX * newZoom;
    const newPanY = centerY - contentY * newZoom;
    
    setPreviewZoom(newZoom);
    setPreviewPan({ x: newPanX, y: newPanY });
  }, [previewZoom, previewPan, previewWidth, previewHeight]);
  
  const zoomOut = useCallback(() => {
    const zoomFactor = 1.2;
    const newZoom = Math.max(previewZoom / zoomFactor, 0.1);
    
    // Zoom centered on viewport center
    const centerX = previewWidth / 2;
    const centerY = previewHeight / 2;
    
    // Content point at viewport center
    const contentX = (centerX - previewPan.x) / previewZoom;
    const contentY = (centerY - previewPan.y) / previewZoom;
    
    // New pan to keep center point centered
    const newPanX = centerX - contentX * newZoom;
    const newPanY = centerY - contentY * newZoom;
    
    setPreviewZoom(newZoom);
    setPreviewPan({ x: newPanX, y: newPanY });
  }, [previewZoom, previewPan, previewWidth, previewHeight]);
  
  const resetViewport = useCallback(() => {
    setPreviewZoom(1);
    setPreviewPan({ x: 0, y: 0 });
  }, []);
  
  const fitContent = useCallback(() => {
    if (shapes.length === 0) return;
    
    // Calculate bounding box of all shapes
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    shapes.forEach((shape, idx) => {
      const settings = shapeSettings[idx] || { enabled: true };
      if (!settings.enabled || !isLayerEnabled(shape.layer)) return;
      if (shape.bbox) {
        minX = Math.min(minX, shape.bbox.minX);
        minY = Math.min(minY, shape.bbox.minY);
        maxX = Math.max(maxX, shape.bbox.maxX);
        maxY = Math.max(maxY, shape.bbox.maxY);
      }
    });
    
    if (minX === Infinity) return;
    
    const contentWidth = maxX - minX;
    const contentHeight = maxY - minY;
    const baseScale = previewWidth / canvasWidth;
    
    // Calculate zoom to fit content with padding
    const padding = 40;
    const availableWidth = previewWidth - padding * 2;
    const availableHeight = previewHeight - padding * 2;
    
    const zoomX = availableWidth / (contentWidth * baseScale);
    const zoomY = availableHeight / (contentHeight * baseScale);
    const newZoom = Math.min(zoomX, zoomY, 5); // Cap at 5x
    
    // Calculate pan to center content
    const centerX = (minX + maxX) / 2 * baseScale;
    const centerY = (minY + maxY) / 2 * baseScale;
    const panX = (previewWidth / 2) - centerX * newZoom;
    const panY = (previewHeight / 2) - centerY * newZoom;
    
    setPreviewZoom(newZoom);
    setPreviewPan({ x: panX, y: panY });
  }, [shapes, shapeSettings, previewWidth, previewHeight, canvasWidth, isLayerEnabled]);
  
  // Reset layout to single column mode with sections in order
  const resetLayout = useCallback(() => {
    const orderedSections = ['preview', 'project', 'import', 'canvas', 'screens', 'layers', 'shapes'];
    const allLeftColumns = {
      preview: 'left',
      project: 'left',
      import: 'left',
      canvas: 'left',
      screens: 'left',
      layers: 'left',
      shapes: 'left'
    };
    setSectionOrder(orderedSections);
    setSectionColumns(allLeftColumns);
    setSideBySidePreview(false);
    setPreviewSpanColumns(false);
    // Also save this as the saved layout
    setSavedLayout({
      sectionOrder: orderedSections,
      sectionColumns: allLeftColumns,
      sideBySidePreview: false,
      previewSpanColumns: false
    });
  }, []);
  
  // Set layout to side-by-side mode with preview on right
  const sideBySideLayout = useCallback(() => {
    const orderedSections = ['preview', 'project', 'import', 'canvas', 'screens', 'layers', 'shapes'];
    const sideBySideColumns = {
      preview: 'left',
      project: 'left',
      import: 'right',
      canvas: 'right',
      screens: 'right',
      layers: 'right',
      shapes: 'right'
    };
    setSectionOrder(orderedSections);
    setSectionColumns(sideBySideColumns);
    setSideBySidePreview(true);
    setPreviewSpanColumns(false);
  }, []);
  
  // Save current layout
  const saveLayout = useCallback(() => {
    setSavedLayout({
      sectionOrder: sectionOrder,
      sectionColumns: sectionColumns,
      sideBySidePreview: sideBySidePreview,
      previewSpanColumns: previewSpanColumns
    });
  }, [sectionOrder, sectionColumns, sideBySidePreview, previewSpanColumns]);
  
  // Restore saved layout
  const restoreLayout = useCallback(() => {
    if (!savedLayout) return;
    const filteredOrder = Array.isArray(savedLayout.sectionOrder)
      ? savedLayout.sectionOrder.filter(s => defaultSectionOrder.includes(s))
      : defaultSectionOrder;
    const ensuredOrder = defaultSectionOrder.every(s => filteredOrder.includes(s)) ? filteredOrder : defaultSectionOrder;
    const filteredColumns = {};
    defaultSectionOrder.forEach(s => {
      filteredColumns[s] = savedLayout.sectionColumns?.[s] || defaultSectionColumns[s];
    });
    setSectionOrder(ensuredOrder);
    setSectionColumns(filteredColumns);
    setSideBySidePreview(savedLayout.sideBySidePreview ?? sideBySidePreview);
    setPreviewSpanColumns(savedLayout.previewSpanColumns ?? previewSpanColumns);
  }, [savedLayout]);
  
  const trackSelectedShape = useCallback((shapeIndex = null) => {
    const indexToTrack = shapeIndex !== null ? shapeIndex : previewSelectedShape;
    if (indexToTrack === null || !shapes[indexToTrack]) return;
    
    const shape = shapes[indexToTrack];
    if (!shape.bbox) return;
    
    const baseScale = previewWidth / canvasWidth;
    const centerX = (shape.bbox.minX + shape.bbox.maxX) / 2 * baseScale;
    const centerY = (shape.bbox.minY + shape.bbox.maxY) / 2 * baseScale;
    
    // Calculate pan to center the shape
    const panX = (previewWidth / 2) - centerX * previewZoom;
    const panY = (previewHeight / 2) - centerY * previewZoom;
    
    setPreviewPan({ x: panX, y: panY });
  }, [previewSelectedShape, shapes, previewWidth, previewHeight, canvasWidth, previewZoom]);

  const selectShapeFromPreview = useCallback((shapeIndex) => {
    if (shapeIndex === null || shapeIndex === undefined) return;
    
    clearEditingPoint();
    setLastSelectedShape(shapeIndex);
    setPreviewSelectedShape(shapeIndex);
    
    if (isTrackingEnabled) {
      trackSelectedShape(shapeIndex);
    }
    
    // Keep detected list in sync and visible
    setTimeout(() => {
      const row = shapesTableRef.current?.querySelector(`[data-shape-index=\"${shapeIndex}\"]`);
      if (row) {
        row.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
      }
    }, 0);
  }, [clearEditingPoint, isTrackingEnabled, trackSelectedShape]);

  const handleShapeRowClick = useCallback((shapeIndex) => {
    setLastSelectedShape(prev => {
      const next = prev === shapeIndex ? null : shapeIndex;
      setPreviewSelectedShape(next);
      if (isTrackingEnabled && next !== null) {
        trackSelectedShape(next);
      }
      return next;
    });
  }, [isTrackingEnabled, trackSelectedShape]);
  
  // Track selected shape (called manually from preview viewport clicks)
  // Removed auto-tracking to only track when shapes are clicked in viewport
  
  // Calculate arrow direction for a section pointing to the next section
  // Fixed logical order: project → import → canvas → screens → shapes → preview
  const logicalOrder = ['project', 'import', 'canvas', 'screens', 'layers', 'shapes', 'preview'];
  
  const getArrowForSection = (sectionId) => {
    const currentLogicalIndex = logicalOrder.indexOf(sectionId);
    
    // Last section (preview) or not found - show diamond
    if (currentLogicalIndex === -1 || currentLogicalIndex === logicalOrder.length - 1) {
      return '◇';
    }
    
    const nextSectionId = logicalOrder[currentLogicalIndex + 1];
    const currentColumn = sectionColumns[sectionId] || 'left';
    const nextColumn = sectionColumns[nextSectionId] || 'left';
    
    // In single column mode, check visual order
    if (!sideBySidePreview) {
      const currentVisualIndex = sectionOrder.indexOf(sectionId);
      const nextVisualIndex = sectionOrder.indexOf(nextSectionId);
      return nextVisualIndex > currentVisualIndex ? '↓' : '↑';
    }
    
    // Get positions within columns (visual positions)
    const leftSections = sectionOrder.filter(id => (sectionColumns[id] || 'left') === 'left');
    const rightSections = sectionOrder.filter(id => sectionColumns[id] === 'right');
    
    const currentIndexInColumn = currentColumn === 'left' 
      ? leftSections.indexOf(sectionId) 
      : rightSections.indexOf(sectionId);
    const nextIndexInColumn = nextColumn === 'left' 
      ? leftSections.indexOf(nextSectionId) 
      : rightSections.indexOf(nextSectionId);
    
    // Same column - check if up or down
    if (currentColumn === nextColumn) {
      return nextIndexInColumn > currentIndexInColumn ? '↓' : '↑';
    }
    
    // Moving to right column
    if (currentColumn === 'left' && nextColumn === 'right') {
      if (nextIndexInColumn < currentIndexInColumn) {
        return '↗'; // Up and right
      } else if (nextIndexInColumn > currentIndexInColumn) {
        return '↘'; // Down and right
      }
      return '→'; // Same row - straight right
    }
    
    // Moving to left column
    if (currentColumn === 'right' && nextColumn === 'left') {
      if (nextIndexInColumn < currentIndexInColumn) {
        return '↖'; // Up and left
      } else if (nextIndexInColumn > currentIndexInColumn) {
        return '↙'; // Down and left
      }
      return '←'; // Same row - straight left
    }
    
    return '↓'; // Default
  };
  
  // Section configuration with fixed numbers
  const sectionConfigs = {
    project: { title: 'Project', number: 1 },
    import: { title: 'Import Artwork', number: 2 },
    canvas: { title: 'Canvas Size', number: 3 },
    screens: { title: 'Screens', number: 4 },
    layers: { title: 'Layers', number: 5 },
    shapes: { title: 'Detected Shapes', number: 6 },
    preview: { title: 'Preview', number: 7 }
  };

  const sectionIconMap = {
    project: ["M4 6h4l2 2h10v10H4z", "M4 6l0 12"],
    import: ["M12 16V4", "M7 11l5 5 5-5", "M5 18h14"],
    canvas: ["M5 5h4v2H7v2H5z", "M19 5h-4v2h2v2h2z", "M5 19h4v-2H7v-2H5z", "M19 19h-4v-2h2v-2h2z", "M9 9h6v6H9z"],
    screens: ["M4 6h16v10H4z", "M9 18h6"],
    layers: ["M5 7h14v3H5z", "M7 11h10v3H7z", "M9 15h6v3H9z"],
    shapes: ["M12 4l6 4v8l-6 4-6-4V8z", "M12 8v8", "M8 10l4 2 4-2"],
    preview: ["M5 12s2.5-5 7-5 7 5 7 5-2.5 5-7 5-7-5-7-5z", "M12 9.5a2.5 2.5 0 1 0 0 5 2.5 2.5 0 0 0 0-5z"]
  };

  const sectionIconSize = { import: 20 };
  const sectionIconBox = { import: 36 };

  const renderSectionIcon = (id) => {
    const paths = sectionIconMap[id];
    if (!paths) return null;
    const iconSize = sectionIconSize[id] || 18;
    const boxSize = sectionIconBox[id] || 32;
    return (
      <span style={{ ...themeStyles.sectionIconWrapper, width: boxSize, height: boxSize }} aria-hidden="true">
        <svg viewBox="0 0 24 24" style={{ ...themeStyles.sectionIcon, width: iconSize, height: iconSize }} role="presentation">
          {paths.map((d, i) => <path key={i} d={d} />)}
        </svg>
      </span>
    );
  };
  
  // Collapsible Section component
  // Render a collapsible section (not a component to avoid re-mounting on state changes)
  const renderCollapsibleSection = (id, children, extra, column) => {
    const config = sectionConfigs[id];
    const isCollapsed = collapsedSections[id];
    const isDragging = draggedSection === id;
    const currentColumn = sectionColumns[id] || 'left';
    
    // Preview section needs overflow visible to show canvas border properly
    const isPreview = id === 'preview';
    
    return (
      <div 
        key={id}
        className="p-card pp-panel"
        style={{
          ...themeStyles.section,
          ...(isDragging ? themeStyles.sectionDragging : {}),
          ...(isCollapsed ? themeStyles.sectionCollapsed : {}),
          ...(isPreview ? { overflow: 'visible' } : {})
        }}
        onDragOver={(e) => handleDragOver(e, id, column)}
      >
        <div 
          className="p-toolbar"
          style={themeStyles.sectionHeader}
          onClick={() => toggleSection(id)}
          draggable={true}
          onDragStart={(e) => handleDragStart(e, id)}
          onDragEnd={handleDragEnd}
        >
          <span style={themeStyles.dragHandle} title="Drag to reorder">⋮⋮</span>
          {renderSectionIcon(id)}
          <span style={themeStyles.sectionTitleText}>{config.title}</span>
          {/* Column move buttons - only show in side-by-side mode */}
          {sideBySidePreview && (
            <span style={themeStyles.columnMoveButtons} onClick={(e) => e.stopPropagation()}>
              <button className="p-btn"
                onClick={() => moveToColumn(id, 'left')}
                style={{
                  ...themeStyles.columnMoveBtn,
                  ...(currentColumn === 'left' ? themeStyles.columnMoveBtnActive : themeStyles.columnMoveBtnInactive)
                }}
                title="Move to left column"
              >
                ◀
              </button>
              <button className="p-btn"
                onClick={() => moveToColumn(id, 'right')}
                style={{
                  ...themeStyles.columnMoveBtn,
                  ...(currentColumn === 'right' ? themeStyles.columnMoveBtnActive : themeStyles.columnMoveBtnInactive)
                }}
                title="Move to right column"
              >
                ▶
              </button>
            </span>
          )}
          {extra}
          <span style={themeStyles.collapseIcon}>{isCollapsed ? '▶' : '▼'}</span>
        </div>
        {!isCollapsed && (
          <div style={{
            ...themeStyles.sectionContent,
            ...(isPreview ? { overflow: 'visible' } : {})
          }}>
            {children}
          </div>
        )}
      </div>
    );
  };

  // Get sections to render, split by column
  const leftColumnSections = sectionOrder.filter(id => {
    if (!sideBySidePreview) return true; // Single column mode - all in left
    if (id === 'preview' && previewSpanColumns) return false; // Preview spanning both
    return sectionColumns[id] === 'left';
  });
  
  const rightColumnSections = sectionOrder.filter(id => {
    if (!sideBySidePreview) return false; // Single column mode - nothing in right
    if (id === 'preview' && previewSpanColumns) return false; // Preview spanning both
    return sectionColumns[id] === 'right';
  });

  const isDraggingSection = draggedSection !== null;
  
  // Check if preview should span both columns
  const previewIsSpanning = sideBySidePreview && previewSpanColumns;

  // Render section content based on section ID
  const renderSectionContent = (sectionId) => {
    switch (sectionId) {
      case 'project':
        return (
          <div style={{display: 'flex', flexDirection: 'column', gap: '16px', minHeight: '100%'}}>
            <input
              ref={projectInputRef}
              type="file"
              accept=".rslm"
              onChange={loadProject}
              style={themeStyles.hiddenInput}
            />
            <div style={themeStyles.importRow}>
              <div style={{display: 'flex', flexDirection: 'column', gap: '4px'}}>
                <span style={themeStyles.inlineLabel}>Project File</span>
                <div style={themeStyles.buttonGroup}>
                  <button className="p-btn" onClick={newProject} style={themeStyles.presetButton}>New</button>
                  <button className="p-btn" onClick={() => projectInputRef.current?.click()} style={themeStyles.presetButton}>Open</button>
                  <button className="p-btn" onClick={saveProject} disabled={!svgText} style={{...themeStyles.presetButton, ...(svgText ? {} : themeStyles.buttonDisabled)}}>Save</button>
                </div>
              </div>
              <div style={{display: 'flex', flexDirection: 'column', gap: '4px'}}>
                <span style={themeStyles.inlineLabel}>Layout</span>
                <div style={themeStyles.buttonGroup}>
                  <button className="p-btn" 
                    onClick={resetLayout} 
                    style={{
                      ...themeStyles.presetButton,
                      ...(!sideBySidePreview ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                    }}
                  >
                    Single Column
                  </button>
                  <button className="p-btn" 
                    onClick={sideBySideLayout} 
                    style={{
                      ...themeStyles.presetButton,
                      ...(sideBySidePreview && !previewSpanColumns ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                    }}
                  >
                    Split View
                  </button>
                  <button className="p-btn" onClick={saveLayout} style={themeStyles.presetButton}>Save Layout</button>
                  {savedLayout && (
                    <button className="p-btn" 
                      onClick={restoreLayout} 
                      style={{
                        ...themeStyles.presetButton,
                        ...(savedLayout && 
                          JSON.stringify(sectionOrder) === JSON.stringify(savedLayout.sectionOrder) &&
                          JSON.stringify(sectionColumns) === JSON.stringify(savedLayout.sectionColumns) &&
                          sideBySidePreview === savedLayout.sideBySidePreview &&
                          previewSpanColumns === savedLayout.previewSpanColumns
                          ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                      }}
                    >
                      Restore Saved
                    </button>
                  )}
                </div>
              </div>
            </div>
            <div style={themeStyles.importRow}>
              <div style={{display: 'flex', flexDirection: 'column', gap: '4px'}}>
                <span style={themeStyles.inlineLabel}>Project Name</span>
                <input className="p-form-text"
                  type="text"
                  value={projectName}
                  onChange={(e) => handleProjectNameInput(e.target.value)}
                  onClick={(e) => e.stopPropagation()}
                  onMouseDown={(e) => e.stopPropagation()}
                  onFocus={(e) => e.stopPropagation()}
                  onKeyDown={(e) => e.stopPropagation()}
                  draggable={false}
                  placeholder={fileName || 'Untitled'}
                  style={{...themeStyles.textInput, minWidth: '140px', maxWidth: '200px'}}
                />
              </div>
              <div style={{display: 'flex', flexDirection: 'column', gap: '4px'}}>
                <span style={themeStyles.inlineLabel}>Naming Source</span>
                <div style={themeStyles.buttonGroup}>
                  <button className="p-btn"
                    onClick={() => handleNameSourceChange('custom')}
                    style={{
                      ...themeStyles.presetButton,
                      ...(nameSource === 'custom' ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                    }}
                    title="Use a custom project name"
                  >
                    Custom
                  </button>
                  <button className="p-btn"
                    onClick={() => handleNameSourceChange('title')}
                    style={{
                      ...themeStyles.presetButton,
                      ...(nameSource === 'title' ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                    }}
                    title="Use the document title from XMP metadata or the SVG title element"
                  >
                    Document Title
                  </button>
                  <button className="p-btn"
                    onClick={() => handleNameSourceChange('filename')}
                    style={{
                      ...themeStyles.presetButton,
                      ...(nameSource === 'filename' ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                    }}
                    title="Use the imported file name"
                  >
                    File Name
                  </button>
                </div>
              </div>
            </div>
            <div style={{...themeStyles.exportRow, marginTop: 'auto', width: '100%'}}>
              <button className="p-btn"
                onClick={downloadXml}
                disabled={shapes.length === 0}
                style={{
                  ...themeStyles.arenaExportButton,
                  width: '100%',
                  textAlign: 'center',
                  ...(shapes.length === 0 ? themeStyles.buttonDisabled : {})
                }}
                onMouseEnter={(e) => Object.assign(e.currentTarget.style, themeStyles.arenaExportButtonHover)}
                onMouseLeave={(e) => Object.assign(e.currentTarget.style, themeStyles.arenaExportButton)}
              >
                Export Resolume Arena XML
              </button>
            </div>
          </div>
        );
      case 'import':
        return (
          <>
            <input
              ref={fileInputRef}
              type="file"
              accept=".svg,.svgz,.dxf"
              onChange={handleFileUpload}
              style={themeStyles.hiddenInput}
            />
            <div style={themeStyles.importRow}>
              <div style={themeStyles.importGroup}>
                <span style={themeStyles.inlineLabel}>Source File</span>
                <label 
                  onClick={() => fileInputRef.current?.click()}
                  style={themeStyles.importButtonLabel}
                >
                  Select SVG or DXF File
                </label>
              </div>
              <div style={themeStyles.importGroup}>
                <span style={themeStyles.inlineLabel}>Slice Naming</span>
                <div style={themeStyles.buttonGroup}>
                  <button className="p-btn"
                    onClick={() => toggleShapeNameOption('type')}
                    style={{
                      ...themeStyles.presetButton,
                      ...(shapeNameMode.type ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                    }}
                    title="Use the shape type for slice names"
                  >
                    Shape Type
                  </button>
                  <button className="p-btn"
                    onClick={() => toggleShapeNameOption('title')}
                    style={{
                      ...themeStyles.presetButton,
                      ...(shapeNameMode.title ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                    }}
                    title="Use the SVG title attribute for slice names"
                  >
                    Title Attribute
                  </button>
                </div>
              </div>
              <div style={themeStyles.importGroup}>
                <span style={themeStyles.inlineLabel}>Curve Detail</span>
                <input className="p-form-number"
                  type="number"
                  min="2"
                  max="100"
                  value={bezierResolution}
                  onChange={(e) => handleBezierResolutionChange(Number(e.target.value))}
                  onClick={(e) => e.stopPropagation()}
                  onMouseDown={(e) => e.stopPropagation()}
                  onFocus={(e) => e.stopPropagation()}
                  onKeyDown={(e) => e.stopPropagation()}
                  draggable={false}
                  style={{...themeStyles.numberInput, width: '60px'}}
                  title="Resolution for rasterizing curves"
                />
              </div>
              <div style={themeStyles.importGroup}>
                <span style={themeStyles.inlineLabel}>Shape Cleanup</span>
                <div style={themeStyles.buttonGroup}>
                  <button className="p-btn"
                    onClick={() => handleAutoCloseOpenPathsChange(!autoCloseOpenPaths)}
                    style={{
                      ...themeStyles.presetButton,
                      ...(autoCloseOpenPaths ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                    }}
                    title="Automatically close open paths by connecting start and end points"
                  >
                    Close Open Paths
                  </button>
                  <button className="p-btn"
                    onClick={() => handleExtractClipPathsChange(!extractClipPaths)}
                    style={{
                      ...themeStyles.presetButton,
                      ...(extractClipPaths ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                    }}
                    title="Import shapes that are defined inside clip paths and masks"
                  >
                    Include Clip Paths
                  </button>
                  <button className="p-btn"
                    onClick={() => handleSkipStrokeOnlyChange(!skipStrokeOnly)}
                    style={{
                      ...themeStyles.presetButton,
                      ...(skipStrokeOnly ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                    }}
                    title="Ignore stroke-only paths (fill=none with stroke) that do not export cleanly as filled slices"
                  >
                    Ignore Stroke-Only
                  </button>
                  <button className="p-btn"
                    onClick={handleToggleShapesWithIssues}
                    disabled={!shapesWithIssuesInfo.hasIssues}
                    style={{
                      ...themeStyles.presetButton,
                      ...(shapesWithIssuesInfo.hasEnabledIssues ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive),
                      opacity: shapesWithIssuesInfo.hasIssues ? 1 : 0.5,
                      cursor: shapesWithIssuesInfo.hasIssues ? 'pointer' : 'default'
                    }}
                    title={shapesWithIssuesInfo.hasIssues 
                      ? (shapesWithIssuesInfo.hasEnabledIssues 
                        ? "Disable flagged shapes (open paths or self-intersections)" 
                        : "Re-enable flagged shapes")
                      : "No flagged shapes detected"}
                  >
                    Flagged Shapes
                  </button>
                </div>
              </div>
            </div>
          </>
        );
      case 'canvas':
        return (
          <>
            <div style={themeStyles.presetRow}>
              {presets.map((preset) => (
                <button className="p-btn"
                  key={preset.name}
                  onClick={() => {
                    handleCanvasChange(preset.width, preset.height);
                    setUseArtboard(false); // Disable artboard mode when manually selecting a preset
                  }}
                  style={{
                    ...themeStyles.presetButton,
                    ...(!useArtboard && canvasWidth === preset.width && canvasHeight === preset.height ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                  }}
                >
                  {preset.name}
                </button>
              ))}
              <button className="p-btn"
                onClick={() => setDefaultCanvasSize({ width: canvasWidth, height: canvasHeight })}
                style={{
                  ...themeStyles.presetButton,
                  ...(canvasWidth === defaultCanvasSize.width && canvasHeight === defaultCanvasSize.height 
                    ? themeStyles.presetButtonActive 
                    : themeStyles.presetButtonInactive)
                }}
                title={`Current default: ${defaultCanvasSize.width}×${defaultCanvasSize.height}`}
              >
                Save as Default
              </button>
              <button className="p-btn"
                onClick={() => {
                  // Always enable the setting and apply artboard size
                  setUseArtboard(true);
                  applyArtboardSize();
                }}
                style={{
                  ...themeStyles.presetButton,
                  ...(useArtboard ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                }}
                title="Apply artboard size from SVG. When active, new imports will auto-use artboard size."
              >
                Match SVG Artboard
              </button>
            </div>
            <div style={themeStyles.inputRow}>
              <div style={themeStyles.inputGroup}>
                <label style={themeStyles.label}>Width</label>
                <input className="p-form-number"
                  type="number"
                  value={canvasWidth}
                  onChange={(e) => handleCanvasChange(Number(e.target.value), canvasHeight)}
                  onClick={(e) => e.stopPropagation()}
                  onMouseDown={(e) => e.stopPropagation()}
                  onFocus={(e) => e.stopPropagation()}
                  onKeyDown={(e) => e.stopPropagation()}
                  draggable={false}
                  style={themeStyles.numberInput}
                />
              </div>
              <div style={themeStyles.inputGroup}>
                <label style={themeStyles.label}>Height</label>
                <input className="p-form-number"
                  type="number"
                  value={canvasHeight}
                  onChange={(e) => handleCanvasChange(canvasWidth, Number(e.target.value))}
                  onClick={(e) => e.stopPropagation()}
                  onMouseDown={(e) => e.stopPropagation()}
                  onFocus={(e) => e.stopPropagation()}
                  onKeyDown={(e) => e.stopPropagation()}
                  draggable={false}
                  style={themeStyles.numberInput}
                />
              </div>
              <div style={themeStyles.inputGroup}>
                <label style={themeStyles.label}>Inner Margin (px)</label>
                <input className="p-form-number"
                  type="number"
                  min="0"
                  value={innerMargin}
                  onChange={(e) => handleInnerMarginChange(Number(e.target.value))}
                  onClick={(e) => e.stopPropagation()}
                  onMouseDown={(e) => e.stopPropagation()}
                  onFocus={(e) => e.stopPropagation()}
                  onKeyDown={(e) => e.stopPropagation()}
                  draggable={false}
                  style={themeStyles.numberInput}
                />
              </div>
              <div style={{...themeStyles.inputGroup, justifyContent: 'flex-end'}}>
                <button className="p-btn"
                  onClick={() => handleScaleToFitChange(!scaleToFit)}
                  style={{
                    ...themeStyles.presetButton,
                    ...(scaleToFit ? themeStyles.presetButtonActive : themeStyles.presetButtonInactive)
                  }}
                >
                  Scale to Fit
                </button>
              </div>
            </div>
          </>
        );
      case 'screens':
        return (
          <>
            <div style={themeStyles.screensContainer}>
              {screens.map((screen) => (
                <div key={screen.id} style={themeStyles.screenItem}>
                  <input className="p-form-text"
                    type="text"
                    value={screen.name}
                    onChange={(e) => renameScreen(screen.id, e.target.value)}
                    onClick={(e) => e.stopPropagation()}
                    onMouseDown={(e) => e.stopPropagation()}
                    onFocus={(e) => e.stopPropagation()}
                    onKeyDown={(e) => e.stopPropagation()}
                    draggable={false}
                    style={themeStyles.screenNameInput}
                  />
                  <input className="p-form-number"
                    type="number"
                    value={screen.width || canvasWidth}
                    onChange={(e) => updateScreenSize(screen.id, Number(e.target.value), screen.height || canvasHeight)}
                    onClick={(e) => e.stopPropagation()}
                    onMouseDown={(e) => e.stopPropagation()}
                    onFocus={(e) => e.stopPropagation()}
                    onKeyDown={(e) => e.stopPropagation()}
                    draggable={false}
                    style={themeStyles.screenSizeInput}
                  />
                  <span style={themeStyles.screenSizeX}>×</span>
                  <input className="p-form-number"
                    type="number"
                    value={screen.height || canvasHeight}
                    onChange={(e) => updateScreenSize(screen.id, screen.width || canvasWidth, Number(e.target.value))}
                    onClick={(e) => e.stopPropagation()}
                    onMouseDown={(e) => e.stopPropagation()}
                    onFocus={(e) => e.stopPropagation()}
                    onKeyDown={(e) => e.stopPropagation()}
                    draggable={false}
                    style={themeStyles.screenSizeInput}
                  />
                  <button className="p-btn" onClick={() => applyCanvasSizeToScreen(screen.id)} style={themeStyles.screenResetBtn}>Match Canvas</button>
                  {screens.length > 1 && (
                    <button className="p-btn" onClick={() => removeScreen(screen.id)} style={themeStyles.screenRemoveBtn}>Remove</button>
                  )}
                  <span style={themeStyles.screenShapeCount}>
                    {shapes.filter((shape, i) => {
                      const settings = shapeSettings[i] || {};
                      return settings.enabled && isLayerEnabled(shape.layer) && settings.screen === screen.id;
                    }).length} assigned
                  </span>
                </div>
              ))}
            </div>
            <button className="p-btn" onClick={addScreen} style={themeStyles.addScreenBtn}>Add Screen</button>
          </>
        );
      case 'layers': {
        if (layerStats.length === 0) {
          return (
            <div style={themeStyles.emptyShapesState}>
              <span style={themeStyles.emptyShapesText}>No layers detected</span>
              <span style={themeStyles.emptyShapesHint}>Import an SVG/DXF with layers to manage visibility</span>
            </div>
          );
        }
        const allVisible = layerStats.every(layer => isLayerEnabled(layer.name));
        const noneVisible = layerStats.every(layer => !isLayerEnabled(layer.name));
        return (
          <>
            <div style={{...themeStyles.shapesToolbar, marginBottom: '8px'}}>
              <div style={themeStyles.buttonGroup}>
                <button className="p-btn"
                  onClick={() => setAllLayersVisibility(true)}
                  style={{
                    ...themeStyles.toggleButton,
                    ...(allVisible ? themeStyles.toggleButtonActive : themeStyles.toggleButtonInactive)
                  }}
                >
                  Show All
                </button>
                <button className="p-btn"
                  onClick={() => setAllLayersVisibility(false)}
                  style={{
                    ...themeStyles.toggleButton,
                    ...(noneVisible ? themeStyles.toggleButtonActive : themeStyles.toggleButtonInactive)
                  }}
                >
                  Hide All
                </button>
              </div>
            </div>
            <div style={themeStyles.shapesTable}>
              <div style={themeStyles.shapesTableHeader}>
                <span style={{flex: 1}}>Layer</span>
                <span style={{width: '90px', textAlign: 'center'}}>Active/Total</span>
                <span style={{width: '70px', textAlign: 'center'}}>Slices</span>
                <span style={{width: '70px', textAlign: 'center'}}>Masks</span>
                <span style={{width: '70px', textAlign: 'center'}}>Render</span>
              </div>
              <div style={{...themeStyles.shapesTableBody, maxHeight: '220px'}}>
                {layerStats.map(layer => {
                  const isVisible = isLayerEnabled(layer.name);
                  const renderedEnabled = isVisible ? layer.enabled : 0;
                  const renderedSlices = isVisible ? layer.slices : 0;
                  const renderedMasks = isVisible ? layer.masks : 0;
                  return (
                    <div key={layer.name} style={{...themeStyles.shapeRow, ...(isVisible ? {} : themeStyles.shapeRowDisabled)}}>
                      <span style={{flex: 1, fontWeight: 600, overflow: 'hidden', textOverflow: 'ellipsis'}} title={layer.name}>{layer.name}</span>
                      <span style={{width: '90px', textAlign: 'center'}}>{renderedEnabled}/{layer.total}</span>
                      <span style={{width: '70px', textAlign: 'center'}}>{renderedSlices}</span>
                      <span style={{width: '70px', textAlign: 'center'}}>{renderedMasks}</span>
                      <span style={{width: '70px', textAlign: 'center'}}>
                        <button className="p-btn"
                          onClick={() => toggleLayerVisibility(layer.name)}
                          style={{
                            ...themeStyles.toggleButton,
                            ...(isVisible ? themeStyles.toggleButtonActive : themeStyles.toggleButtonInactive),
                            width: '100%'
                          }}
                        >
                          {isVisible ? 'Hide' : 'Show'}
                        </button>
                      </span>
                    </div>
                  );
                })}
              </div>
            </div>
          </>
        );
      }
      case 'shapes':
        if (shapes.length === 0) {
          return (
            <div style={themeStyles.emptyShapesState}>
              <span style={themeStyles.emptyShapesText}>No shapes detected</span>
              <span style={themeStyles.emptyShapesHint}>Import a file to populate the table</span>
            </div>
          );
        }
        return (
          <>
            <div style={themeStyles.shapesToolbar}>
              <div style={themeStyles.outputTypeGroup}>
                <label style={themeStyles.label}>Default Output Type</label>
                <div style={themeStyles.outputTypeButtons}>
                  <button className="p-btn"
                    onClick={() => setDefaultOutputType('slice')}
                    style={{...themeStyles.outputTypeBtn, ...(defaultOutputType === 'slice' ? themeStyles.outputTypeBtnActive : themeStyles.outputTypeBtnInactive)}}
                  >
                    Slice
                  </button>
                  <button className="p-btn"
                    onClick={() => setDefaultOutputType('mask')}
                    style={{...themeStyles.outputTypeBtn, ...(defaultOutputType === 'mask' ? themeStyles.outputTypeBtnActive : themeStyles.outputTypeBtnInactive)}}
                  >
                    Mask
                  </button>
                  <button className="p-btn"
                    onClick={() => setDefaultOutputType('both')}
                    style={{...themeStyles.outputTypeBtn, ...(defaultOutputType === 'both' ? themeStyles.outputTypeBtnActive : themeStyles.outputTypeBtnInactive)}}
                  >
                    Both
                  </button>
                </div>
              </div>
              <button className="p-btn" 
                onClick={() => setCombineMasks(!combineMasks)} 
                style={{...themeStyles.outputTypeBtn, ...(combineMasks ? themeStyles.outputTypeBtnActive : themeStyles.outputTypeBtnInactive)}}
                title="Merge all masks into one layer per screen"
              >
                Merge Masks
              </button>
              <button className="p-btn" onClick={applyDefaultToAll} style={themeStyles.applyAllBtn}>Apply Defaults</button>
              <button className="p-btn" onClick={toggleAllEnabled} style={themeStyles.toggleBtn}>
                {shapes.every((_, i) => shapeSettings[i]?.enabled) ? 'Disable All' : 'Enable All'}
              </button>
              <div style={{display: 'flex', alignItems: 'center', gap: '6px', marginLeft: 'auto'}}>
                <label style={themeStyles.label}>List Filter</label>
                <div style={themeStyles.buttonGroup}>
                  <button
                    className="p-btn"
                    onClick={() => setShapesLayerFilter('visible')}
                    style={{
                      ...themeStyles.toggleButton,
                      ...(shapesLayerFilter === 'visible' ? themeStyles.toggleButtonActive : themeStyles.toggleButtonInactive)
                    }}
                    title="Show only shapes whose layers are currently visible"
                  >
                    Visible Layers
                  </button>
                  <button
                    className="p-btn"
                    onClick={() => setShapesLayerFilter('all')}
                    style={{
                      ...themeStyles.toggleButton,
                      ...(shapesLayerFilter === 'all' ? themeStyles.toggleButtonActive : themeStyles.toggleButtonInactive)
                    }}
                    title="Show all shapes regardless of layer visibility"
                  >
                    All Layers
                  </button>
                </div>
              </div>
            </div>
            
            <div style={themeStyles.shapesTable}>
              <div style={themeStyles.shapesTableHeader}>
                <span style={{width: '36px', textAlign: 'center'}}>✓</span>
                <span style={{flex: 1}}>Name</span>
                <span style={{width: '120px', textAlign: 'center'}}>Layer</span>
                <span style={{width: '100px', textAlign: 'center'}}>Screen</span>
                <span style={{width: '50px', textAlign: 'center'}}>Slice</span>
                <span style={{width: '50px', textAlign: 'center'}}>Mask</span>
                <span style={{width: '40px', textAlign: 'center'}}>Invert</span>
                <span style={{width: '40px', textAlign: 'center'}}>Bezier</span>
                <span style={{width: '50px', textAlign: 'right'}}>Points</span>
              </div>
              <div ref={shapesTableRef} style={themeStyles.shapesTableBody}>
                {shapes.map((shape, i) => {
                  const settings = shapeSettings[i] || { enabled: true, slice: true, mask: false, screen: 1, customName: '', invertMask: true, bezierMode: false };
                  const canUseBezier = shape.hasBezierCurves && settings.mask;
                  const layerName = shape.layer || fallbackLayerName;
                  const layerActive = isLayerEnabled(layerName);
                  const passesLayerFilter = shapesLayerFilter === 'all' || layerActive;
                  if (!passesLayerFilter) return null;
                  const isEnabled = settings.enabled && layerActive;
                  const isSelected = lastSelectedShape === i;
                  return (
                    <div 
                      key={i}
                      data-shape-index={i}
                      style={{
                        ...themeStyles.shapeRow, 
                        ...(isEnabled ? {} : themeStyles.shapeRowDisabled),
                        ...(isSelected ? themeStyles.shapeRowSelected : {})
                      }}
                      onClick={() => handleShapeRowClick(i)}
                    >
                      <span style={{width: '36px', textAlign: 'center'}} onClick={(e) => e.stopPropagation()}>
                        <input
                          type="checkbox"
                          checked={settings.enabled}
                          onClick={(e) => e.stopPropagation()}
                          onChange={(e) => { e.stopPropagation(); updateShapeSetting(i, 'enabled', e.target.checked); }}
                          style={themeStyles.checkbox}
                        />
                      </span>
                      <span style={{flex: 1, minWidth: 0}}>
                        <input className="p-form-text"
                          type="text"
                          value={settings.customName || ''}
                          placeholder={shape.name}
                          readOnly
                          title={layerActive ? `Layer: ${layerName}` : `Layer: ${layerName} (layer hidden)`}
                          onClick={(e) => {
                            e.stopPropagation();
                            if (settings.enabled) {
                              const rect = e.target.getBoundingClientRect();
                              setFloatingNameEditor({ shapeIndex: i, rect });
                            }
                          }}
                          onMouseDown={(e) => e.stopPropagation()}
                          disabled={!settings.enabled}
                          style={{...themeStyles.shapeNameInput, ...(settings.enabled ? { cursor: 'pointer' } : {opacity: 0.5})}}
                        />
                      </span>
                      <span style={{width: '120px', textAlign: 'center', color: layerActive ? '#fff' : '#888'}} title={layerName}>
                        {layerName}
                      </span>
                      <span style={{width: '100px', textAlign: 'center'}}>
                        <select className="p-form-select"
                          value={settings.screen || 1}
                          disabled={!settings.enabled}
                          onChange={(e) => updateShapeSetting(i, 'screen', Number(e.target.value))}
                          onClick={(e) => e.stopPropagation()}
                          style={themeStyles.screenSelect}
                        >
                          {screens.map((screen) => (
                            <option key={screen.id} value={screen.id}>{screen.name}</option>
                          ))}
                        </select>
                      </span>
                      <span style={{width: '50px', textAlign: 'center'}}>
                        <input
                          type="checkbox"
                          checked={settings.slice}
                          disabled={!settings.enabled}
                          onChange={(e) => { e.stopPropagation(); updateShapeSetting(i, 'slice', e.target.checked); }}
                          style={themeStyles.checkbox}
                        />
                      </span>
                      <span style={{width: '50px', textAlign: 'center'}}>
                        <input
                          type="checkbox"
                          checked={settings.mask}
                          disabled={!settings.enabled}
                          onChange={(e) => { e.stopPropagation(); updateShapeSetting(i, 'mask', e.target.checked); }}
                          style={themeStyles.checkbox}
                        />
                      </span>
                      <span style={{width: '40px', textAlign: 'center'}}>
                        <input
                          type="checkbox"
                          checked={settings.invertMask !== false}
                          disabled={!settings.enabled || !settings.mask}
                          onChange={(e) => { e.stopPropagation(); updateShapeSetting(i, 'invertMask', e.target.checked); }}
                          onClick={(e) => e.stopPropagation()}
                          style={{...themeStyles.checkbox, ...(settings.mask ? {} : {opacity: 0.3})}}
                          title="Invert Mask"
                        />
                      </span>
                      <span style={{width: '40px', textAlign: 'center'}}>
                        <input
                          type="checkbox"
                          checked={settings.bezierMode || false}
                          disabled={!settings.enabled || !canUseBezier}
                          onChange={(e) => { e.stopPropagation(); updateShapeSetting(i, 'bezierMode', e.target.checked); }}
                          onClick={(e) => e.stopPropagation()}
                          style={{...themeStyles.checkbox, ...(canUseBezier ? {} : {opacity: 0.3})}}
                          title="Use Bezier curves (for masks)"
                        />
                      </span>
                      <span style={themeStyles.pointCount}>{shape.points.length}</span>
                    </div>
                  );
                })}
              </div>
            </div>
            
            <div style={themeStyles.shapeSummary}>
              {(() => {
                const sliceCount = shapes.filter((shape, i) => {
                  const settings = shapeSettings[i] || {};
                  return settings.enabled && settings.slice && isLayerEnabled(shape.layer);
                }).length;
                const maskCount = shapes.filter((shape, i) => {
                  const settings = shapeSettings[i] || {};
                  return settings.enabled && settings.mask && isLayerEnabled(shape.layer);
                }).length;
                const enabledCount = shapes.filter((shape, i) => {
                  const settings = shapeSettings[i] || {};
                  return settings.enabled && isLayerEnabled(shape.layer);
                }).length;
                const screenCount = [...new Set(shapes
                  .map((shape, i) => {
                    const settings = shapeSettings[i] || {};
                    const layerActive = isLayerEnabled(shape.layer);
                    return settings.enabled && layerActive && (settings.slice || settings.mask) ? settings.screen : null;
                  })
                  .filter(Boolean)
                )].length;
                return (
                  <>
                    Ready to export: {enabledCount} shapes → {sliceCount} slices, {maskCount} masks
                    {screens.length > 1 && ` across ${screenCount} screen${screenCount !== 1 ? 's' : ''}`}
                    <span style={{marginLeft: '16px', color: '#888'}}>({enabledCount} of {shapes.length} enabled)</span>
                  </>
                );
              })()}
            </div>
          </>
        );
      default:
        return null;
    }
  };

  // Get extra content for section headers
  const getSectionExtra = (sectionId) => {
    switch (sectionId) {
      case 'import':
        return null;
      case 'screens':
        return null;
      case 'shapes':
        return null;
      default:
        return null;
    }
  };

  // Preview toolbar component
  const PreviewToolbar = () => (
    <div style={themeStyles.previewToolbar} onClick={(e) => e.stopPropagation()}>
      <button className="p-btn" onClick={zoomOut} style={themeStyles.previewToolbarButton} title="Zoom Out" data-tooltip="Zoom Out">−</button>
      <span style={themeStyles.previewZoomLevel}>{Math.round(previewZoom * 100)}%</span>
      <button className="p-btn" onClick={zoomIn} style={themeStyles.previewToolbarButton} title="Zoom In" data-tooltip="Zoom In">+</button>
      <div style={themeStyles.previewToolbarDivider} />
      <button className="p-btn" onClick={resetViewport} style={themeStyles.previewToolbarButton} title="Reset Viewport" data-tooltip="Reset Viewport">⌂</button>
      <button className="p-btn" onClick={fitContent} style={themeStyles.previewToolbarButton} title="Fit Content" data-tooltip="Fit Content">⊡</button>
      <button className="p-btn" 
        onClick={() => setIsTrackingEnabled(!isTrackingEnabled)} 
        style={{
          ...themeStyles.previewToolbarButton,
          ...(isTrackingEnabled ? themeStyles.previewToolbarButtonActive : themeStyles.previewToolbarButtonInactive)
        }} 
        title="Track Selected Shape"
        data-tooltip="Track Selected Shape"
      >
        ◎
      </button>
      <button className="p-btn" 
        onClick={() => setShowPointNumbers(!showPointNumbers)} 
        style={{
          ...themeStyles.previewToolbarButton,
          ...(showPointNumbers ? themeStyles.previewToolbarButtonActive : themeStyles.previewToolbarButtonInactive)
        }} 
        title="Show point indices"
        data-tooltip="Show point indices"
      >
        N
      </button>
      <div style={themeStyles.previewToolbarDivider} />
      <span style={{...themeStyles.previewZoomLevel, minWidth: 'auto'}}>Filter</span>
      <button className="p-btn" 
        onClick={() => toggleSelectionFilter('slice')}
        style={{
          ...themeStyles.previewToolbarButton,
          ...(selectionFilter.slice ? themeStyles.previewToolbarButtonActive : themeStyles.previewToolbarButtonInactive)
        }}
        title="Enable selection for slice shapes"
        data-tooltip="Enable selection for slice shapes"
      >
        S
      </button>
      <button className="p-btn" 
        onClick={() => toggleSelectionFilter('mask')}
        style={{
          ...themeStyles.previewToolbarButton,
          ...(selectionFilter.mask ? themeStyles.previewToolbarButtonActive : themeStyles.previewToolbarButtonInactive)
        }}
        title="Enable selection for mask shapes"
        data-tooltip="Enable selection for mask shapes"
      >
        M
      </button>
      <button className="p-btn" 
        onClick={() => toggleSelectionFilter('flagged')}
        style={{
          ...themeStyles.previewToolbarButton,
          ...(selectionFilter.flagged ? themeStyles.previewToolbarButtonActive : themeStyles.previewToolbarButtonInactive)
        }}
        title="Enable selection for flagged shapes"
        data-tooltip="Enable selection for flagged shapes"
      >
        !
      </button>
      <div style={themeStyles.previewToolbarDivider} />
      <button className="p-btn" 
        onClick={() => setSideBySidePreview(!sideBySidePreview)} 
        style={{
          ...themeStyles.previewToolbarButton,
          ...(sideBySidePreview ? themeStyles.previewToolbarButtonActive : themeStyles.previewToolbarButtonInactive)
        }} 
        title="Toggle split layout"
        data-tooltip="Toggle split layout"
      >
        ◫
      </button>
      {sideBySidePreview && (
        <button className="p-btn" 
          onClick={() => setPreviewSpanColumns(!previewSpanColumns)} 
          style={{
            ...themeStyles.previewToolbarButton,
            ...(previewSpanColumns ? themeStyles.previewToolbarButtonActive : themeStyles.previewToolbarButtonInactive)
          }} 
          title="Expand preview across both columns"
          data-tooltip="Expand preview across both columns"
        >
          ▭
        </button>
      )}
    </div>
  );

  // Preview content component
  const PreviewContent = ({ width, height, useSvgViewBox = false, useAspectRatio = false }) => {
    // For side-by-side mode, we use viewBox to maintain aspect ratio
    const viewBoxStr = `0 0 ${previewWidth} ${previewHeight}`;
    const aspectRatio = canvasWidth / canvasHeight;
    const hasVisibleShapes = shapes.some((shape, i) => {
      const settings = shapeSettings[i] || {};
      return settings.enabled && isLayerEnabled(shape.layer);
    });
    
    const containerStyle = {
      ...themeStyles.previewContainer, 
      width, 
      cursor: isDraggingPoint ? 'crosshair' : (isPanning ? 'grabbing' : 'grab'),
      ...(useAspectRatio ? { aspectRatio: aspectRatio, height: 'auto' } : { height })
    };
    
    return (
      <div 
        ref={previewContainerRefCallback}
        className="preview-card"
        style={containerStyle}
        onMouseDown={handlePreviewMouseDown}
        onMouseMove={handlePreviewMouseMove}
        onMouseUp={handlePreviewMouseUp}
        onMouseLeave={handlePreviewMouseLeave}
      >
        <svg 
          width={width} 
          height="100%" 
          viewBox={useSvgViewBox ? viewBoxStr : undefined}
          preserveAspectRatio="xMidYMid meet"
          style={themeStyles.previewSvg}
        >
          <defs>
            <pattern id="grid" width={50 * previewZoom} height={50 * previewZoom} patternUnits="userSpaceOnUse" patternTransform={`translate(${previewPan.x % (50 * previewZoom)}, ${previewPan.y % (50 * previewZoom)})`}>
              <path d={`M ${50 * previewZoom} 0 L 0 0 0 ${50 * previewZoom}`} fill="none" stroke="rgba(59, 130, 246, 0.15)" strokeWidth="0.5"/>
            </pattern>
          </defs>
          <rect width={useSvgViewBox ? previewWidth : "100%"} height={useSvgViewBox ? previewHeight : "100%"} fill="url(#grid)" />
        </svg>
        
        <svg 
          width={width} 
          height="100%" 
          viewBox={useSvgViewBox ? viewBoxStr : undefined}
          preserveAspectRatio="xMidYMid meet"
          style={{...themeStyles.previewSvg, position: 'absolute', top: 0, left: 0, overflow: 'hidden'}}
        >
          <g transform={`translate(${previewPan.x}, ${previewPan.y}) scale(${previewZoom})`}>
            {/* Canvas boundary - blue outline */}
            <rect
              x={0}
              y={0}
              width={canvasWidth * scale}
              height={canvasHeight * scale}
              fill="none"
              stroke="#3b82f6"
              strokeWidth={1 / previewZoom}
            />
            
            {shapes.map((shape, i) => {
              const settings = shapeSettings[i] || { enabled: true, slice: true, mask: false };
              const layerEnabled = isLayerEnabled(shape.layer);
              if (!layerEnabled) return null;
              const isEnabled = settings.enabled;
              const hasSlice = settings.slice;
              const hasMask = settings.mask;
              // Use separate preview selection only when tracking is enabled
              const isSelected = isTrackingEnabled ? previewSelectedShape === i : lastSelectedShape === i;
              const isOpen = isShapeOpen(shape.points, shape.bbox, shape.sourceType);
              const isSelfIntersecting = hasSelfIntersection(shape.points, shape.sourceType, shape.isCompoundSubpath);
              const hasIssue = isOpen || isSelfIntersecting;
              const selectionMatches = (() => {
                const anyActive = selectionFilter.slice || selectionFilter.mask || selectionFilter.flagged;
                const matches = (selectionFilter.slice && hasSlice) || (selectionFilter.mask && hasMask) || (selectionFilter.flagged && hasIssue);
                return anyActive ? matches : true;
              })();
              const isVisiblySelected = isSelected && selectionMatches;
              const opacityBase = isEnabled ? 1 : 0.3;
              const opacityFilter = selectionMatches ? 1 : 0.2;
              const canSelect = selectionMatches && isEnabled;
              
              let fillColor = 'rgba(100, 100, 100, 0.2)';
              let strokeColor = '#666';
              
              if (isEnabled) {
                if (hasIssue) {
                  // Shapes with issues (open or self-intersecting) are shown in red as a warning
                  fillColor = 'rgba(239, 68, 68, 0.3)';
                  strokeColor = '#ef4444';
                } else if (hasSlice && hasMask) {
                  fillColor = 'rgba(59, 130, 246, 0.3)';
                  strokeColor = '#a855f7';
                } else if (hasSlice) {
                  fillColor = 'rgba(59, 130, 246, 0.3)';
                  strokeColor = '#3b82f6';
                } else if (hasMask) {
                  fillColor = 'rgba(168, 85, 247, 0.3)';
                  strokeColor = '#a855f7';
                }
              }
              
              if (isVisiblySelected) {
                strokeColor = '#ff9500';
              }
              
              return (
                <g 
                  key={i} 
                  opacity={opacityBase * opacityFilter} 
                >
                  <rect
                    x={shape.bbox.minX * scale}
                    y={shape.bbox.minY * scale}
                    width={(shape.bbox.maxX - shape.bbox.minX) * scale}
                    height={(shape.bbox.maxY - shape.bbox.minY) * scale}
                    fill="transparent"
                    stroke={isVisiblySelected ? '#ff9500' : (hasIssue && isEnabled ? '#ef4444' : '#666')}
                    strokeWidth={isVisiblySelected ? 2 / previewZoom : 1 / previewZoom}
                    strokeDasharray={`${4 / previewZoom} ${2 / previewZoom}`}
                    style={{ cursor: canSelect ? 'pointer' : 'default', pointerEvents: canSelect ? 'auto' : 'none' }}
                    onMouseDown={(e) => {
                      e.stopPropagation();
                      e.preventDefault();
                      if (canSelect) {
                        selectShapeFromPreview(i);
                      }
                    }}
                  />
                  <polygon
                    points={shape.points.map(p => `${p.x * scale},${p.y * scale}`).join(' ')}
                    fill={fillColor}
                    stroke={strokeColor}
                    strokeWidth={2 / previewZoom}
                    style={{ cursor: canSelect ? 'pointer' : 'default', pointerEvents: canSelect ? 'auto' : 'none' }}
                    onMouseDown={(e) => {
                      e.stopPropagation();
                      e.preventDefault();
                      if (canSelect) {
                        selectShapeFromPreview(i);
                      }
                    }}
                  />
                  {shape.points.map((p, j) => {
                    const isEditingThisPoint = editingPoint && editingPoint.shapeIndex === i && editingPoint.pointIndex === j;
                    const isFirstOrLast = j === 0 || j === shape.points.length - 1;
                    
                    // DEBUG: Log points for selected shapes
                    if (isVisiblySelected && j < 5 && shape.name && shape.name.includes('Path')) {
                    }
                    
                    return (
                      <g key={j}>
                        <circle
                          cx={p.x * scale}
                          cy={p.y * scale}
                          r={isEditingThisPoint ? Math.max(0.5, 2 / previewZoom) : Math.max(0.3, 1 / previewZoom)}
                          fill={isEditingThisPoint ? '#ffcc00' : (hasIssue && isEnabled && isFirstOrLast ? '#ef4444' : (isEnabled ? '#fff' : '#666'))}
                          stroke={isEditingThisPoint ? '#fff' : 'none'}
                          strokeWidth={1 / previewZoom}
                          style={{ cursor: canSelect ? 'pointer' : 'default', pointerEvents: canSelect ? 'auto' : 'none' }}
                          onMouseDown={(e) => {
                            if (!canSelect) return;
                            // CMD+click (Mac) or Ctrl+click (Windows) to start editing a point
                            if (e.metaKey || e.ctrlKey) {
                              e.stopPropagation();
                              e.preventDefault();
                              
                              // Calculate offset from mouse to point center (in SVG viewBox coordinates)
                              const rect = previewContainerRef.current?.getBoundingClientRect();
                              if (rect) {
                                const mouseX = e.clientX - rect.left;
                                const mouseY = e.clientY - rect.top;
                                
                                // Account for viewBox scaling
                                const scaleX = previewWidth / rect.width;
                                const scaleY = previewHeight / rect.height;
                                const svgMouseX = mouseX * scaleX;
                                const svgMouseY = mouseY * scaleY;
                                
                                // Point's position in SVG viewBox coordinates (after pan and zoom transform)
                                const pointSvgX = p.x * scale * previewZoom + previewPan.x;
                                const pointSvgY = p.y * scale * previewZoom + previewPan.y;
                                
                                // Offset from mouse to point center in SVG coordinates
                                setDragOffset({
                                  x: svgMouseX - pointSvgX,
                                  y: svgMouseY - pointSvgY
                                });
                              }
                              
                              setEditingPoint({ shapeIndex: i, pointIndex: j });
                              setIsDraggingPoint(true);
                            } else {
                              e.stopPropagation();
                              e.preventDefault();
                              selectShapeFromPreview(i);
                            }
                          }}
                        />
                        {/* Show point number when shape is selected and numbers are enabled */}
                        {isVisiblySelected && showPointNumbers && (
                          <text
                            x={p.x * scale + Math.max(0.5, 1 / previewZoom)}
                            y={p.y * scale - Math.max(0.5, 1 / previewZoom)}
                            fontSize={Math.max(1.5, 3 / previewZoom)}
                            fill={(() => {
                              // 4 shades based on position in shape (cycles through)
                              const shades = ['#ffcc00', '#ff9933', '#ff6666', '#cc99ff'];
                              return shades[j % 4];
                            })()}
                            style={{ pointerEvents: 'none', userSelect: 'none' }}
                          >
                            {j}
                          </text>
                        )}
                      </g>
                    );
                  })}
                </g>
              );
            })}
          </g>
        </svg>
        
        {!hasVisibleShapes && (
          <div style={themeStyles.previewPlaceholder}>
            {shapes.length === 0 ? 'Import a file to view the layout' : 'No visible shapes. Enable layers or shapes to preview.'}
          </div>
        )}
        
        {hasVisibleShapes && (
          <div style={themeStyles.previewLegend}>
            <div style={themeStyles.legendItem}>
              <div style={{...themeStyles.legendDot, backgroundColor: 'rgba(59, 130, 246, 0.5)', border: '2px solid #3b82f6'}}></div>
              <span style={{color: '#3b82f6'}}>Slice</span>
            </div>
            <div style={themeStyles.legendItem}>
              <div style={{...themeStyles.legendDot, backgroundColor: 'rgba(168, 85, 247, 0.5)', border: '2px solid #a855f7'}}></div>
              <span style={{color: '#a855f7'}}>Mask</span>
            </div>
            <div style={themeStyles.legendItem}>
              <div style={{...themeStyles.legendDot, backgroundColor: 'rgba(239, 68, 68, 0.5)', border: '2px solid #ef4444'}}></div>
              <span style={{color: '#ef4444'}}>Flagged</span>
            </div>
            <div style={themeStyles.legendItem}>
              <div style={{...themeStyles.legendDot, backgroundColor: 'transparent', border: '3px solid #3b82f6'}}></div>
              <span style={{color: '#3b82f6'}}>Canvas</span>
            </div>
          </div>
        )}
        
        <div style={themeStyles.previewSize}>
          {canvasWidth} × {canvasHeight}
        </div>
      </div>
    );
  };

  return (
    <div className="p-layout" style={themeStyles.container}>
      <style>{`
        /* Reset any potential constraints */
        html, body {
          width: 100% !important;
          max-width: 100% !important;
          overflow-x: auto !important;
        }
        
        button, label, input, select {
          box-shadow: none !important;
        }
        button::-moz-focus-inner {
          border: 0 !important;
        }
        button:focus-visible, input:focus-visible, select:focus-visible {
          outline: 2px solid var(--accent) !important;
          outline-offset: 2px !important;
        }
        
        /* Main container - single column mode */
        main.single-column {
          position: relative !important;
          z-index: 1 !important;
          width: 100% !important;
          max-width: 100% !important;
          margin: 0 !important;
          padding: 24px 16px 0 16px !important;
          box-sizing: border-box !important;
        }
        
        /* Main container - side by side mode */
        main.side-by-side {
          position: relative !important;
          z-index: 1 !important;
          display: grid !important;
          grid-template-columns: minmax(0, 1fr) minmax(0, 1fr) !important;
          gap: 24px !important;
          width: 100% !important;
          max-width: 100% !important;
          margin: 0 !important;
          padding: 24px 16px 0 16px !important;
          box-sizing: border-box !important;
          align-items: start !important;
          overflow: visible !important;
        }
        
        /* Columns in side-by-side mode */
        main.side-by-side > .layout-column {
          width: 100% !important;
          min-width: 0 !important;
          max-width: 100% !important;
          overflow: visible !important;
          display: flex !important;
          flex-direction: column !important;
          align-content: flex-start !important;
        }
        
        /* Drop zone fills remaining space in column */
        main.side-by-side > .layout-column > .column-drop-zone {
          flex: 1 1 auto !important;
          min-height: 100px !important;
          width: 100% !important;
        }
        
        /* Sections fill their column */
        main.side-by-side > .layout-column > div {
          width: 100% !important;
          min-width: 0 !important;
          max-width: 100% !important;
          box-sizing: border-box !important;
          overflow: hidden !important;
          flex-shrink: 0 !important;
        }
        
        /* Remove bottom margin from last section in column when preview is spanning */
        main.side-by-side > .layout-column > div:last-child {
          margin-bottom: 0 !important;
        }
        
        /* Force all content inside sections to respect container width */
        main.side-by-side > .layout-column > div * {
          max-width: 100% !important;
          box-sizing: border-box !important;
        }
        
        /* Spanning preview container */
        main.side-by-side > .spanning-preview {
          grid-column: 1 / -1;
          width: 100%;
          align-self: start;
        }
        
        main.side-by-side > .empty-drop-zone {
          grid-column: 2;
          width: 100%;
          min-width: 0;
        }

      `}</style>
      <div style={themeStyles.gridOverlay}></div>
      
      {/* Header */}
      <header className="p-toolbar" style={themeStyles.header}>
        <div style={themeStyles.logoSection}>
          <div style={themeStyles.logo}>
            <span style={themeStyles.logoAccent}>Advanced Output Toolkit</span>
            <span style={themeStyles.logoText}>(AOT)</span>
          </div>
          <span style={themeStyles.tagline}>SVG/DXF to Resolume Advanced Output XML</span>
        </div>
        <div style={themeStyles.headerRight}>
          <button
            aria-label="Toggle theme"
            title={theme === 'light' ? 'Switch to dark theme' : 'Switch to light theme'}
            style={themeStyles.themeToggleBtn}
            onClick={() => setTheme(theme === 'light' ? 'dark' : 'light')}
          >
            {theme === 'light' ? (
              <svg width="18" height="18" viewBox="0 0 24 24" fill="currentColor" role="presentation">
                <path d="M21 12.79A9 9 0 1 1 11.21 3 7 7 0 0 0 21 12.79Z" />
              </svg>
            ) : (
              <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" role="presentation">
                <circle cx="12" cy="12" r="5" />
                <line x1="12" y1="1" x2="12" y2="3" />
                <line x1="12" y1="21" x2="12" y2="23" />
                <line x1="4.22" y1="4.22" x2="5.64" y2="5.64" />
                <line x1="18.36" y1="18.36" x2="19.78" y2="19.78" />
                <line x1="1" y1="12" x2="3" y2="12" />
                <line x1="21" y1="12" x2="23" y2="12" />
                <line x1="4.22" y1="19.78" x2="5.64" y2="18.36" />
                <line x1="18.36" y1="5.64" x2="19.78" y2="4.22" />
              </svg>
            )}
          </button>
          {projectName && (
            <span style={themeStyles.projectNameDisplay}>{projectName}</span>
          )}
          <span style={themeStyles.versionBadge}>v1.0</span>
        </div>
      </header>
      
      <main className={sideBySidePreview ? 'side-by-side' : 'single-column'}>
        {/* Left Column */}
        <div 
          data-column="left"
          className="layout-column"
          onDragOver={(e) => { e.preventDefault(); }}
          onDrop={(e) => handleColumnDrop(e, 'left')}
        >
          {leftColumnSections.map(sectionId => {
            // Special handling for preview section
            if (sectionId === 'preview') {
              return renderCollapsibleSection(
                sectionId,
                <PreviewContent 
                  width="100%" 
                  height="auto" 
                  useSvgViewBox={true}
                  useAspectRatio={true}
                />,
                <PreviewToolbar />,
                "left"
              );
            }
            
            return renderCollapsibleSection(
              sectionId,
              renderSectionContent(sectionId),
              getSectionExtra(sectionId),
              "left"
            );
          })}
          {/* Bottom drop zone - fills remaining space in column (only when preview is not spanning) */}
          {sideBySidePreview && !previewIsSpanning && isDraggingSection && (
            <div 
              className="column-drop-zone"
              onDragOver={(e) => { e.preventDefault(); }}
              onDrop={(e) => handleColumnDrop(e, 'left')}
            />
          )}
        </div>
        
        {/* Right Column - only in side-by-side mode */}
        {sideBySidePreview && rightColumnSections.length > 0 && (
          <div 
            data-column="right"
            className="layout-column"
            onDragOver={(e) => { e.preventDefault(); }}
            onDrop={(e) => handleColumnDrop(e, 'right')}
          >
            {rightColumnSections.map(sectionId => {
              // Special handling for preview section
              if (sectionId === 'preview') {
                return renderCollapsibleSection(
                  sectionId,
                  <PreviewContent width="100%" height="auto" useSvgViewBox={true} useAspectRatio={true} />,
                  <PreviewToolbar />,
                  "right"
                );
              }
              
              return renderCollapsibleSection(
                sectionId,
                renderSectionContent(sectionId),
                getSectionExtra(sectionId),
                "right"
              );
            })}
            {/* Bottom drop zone - fills remaining space in column (only when preview is not spanning) */}
            {!previewIsSpanning && isDraggingSection && (
              <div 
                className="column-drop-zone"
                onDragOver={(e) => { e.preventDefault(); }}
                onDrop={(e) => handleColumnDrop(e, 'right')}
              />
            )}
          </div>
        )}
        
        {/* Empty right column drop zone */}
        {sideBySidePreview && rightColumnSections.length === 0 && isDraggingSection && (
          <div 
            className="empty-drop-zone"
            style={themeStyles.emptyColumnDropZone}
            onDragOver={(e) => { e.preventDefault(); }}
            onDrop={(e) => handleColumnDrop(e, 'right')}
          >
            <span style={themeStyles.dropZoneText}>Drag sections here to place them in this column</span>
          </div>
        )}
        
        {/* Spanning Preview - full width below columns */}
        {previewIsSpanning && (
          <div className="spanning-preview" style={themeStyles.spanningPreviewContainer}>
              <div style={{...themeStyles.section, width: '100%'}}>
              <div style={themeStyles.sectionHeader}>
                <span style={themeStyles.dragHandle}>⋮⋮</span>
                {renderSectionIcon('preview')}
                <span style={themeStyles.sectionTitleText}>Preview</span>
                <PreviewToolbar />
                <span style={themeStyles.collapseIcon} onClick={() => toggleSection('preview')}>
                  {collapsedSections['preview'] ? '▶' : '▼'}
                </span>
              </div>
              {!collapsedSections['preview'] && (
                <div style={themeStyles.sectionContent}>
                  <PreviewContent width="100%" height="auto" useSvgViewBox={true} useAspectRatio={true} />
                </div>
              )}
            </div>
          </div>
        )}
      </main>
      
      {/* Floating Name Editor Popup */}
      {floatingNameEditor && (
        <div 
          className="pup-modal-overlay"
          style={themeStyles.floatingNameOverlay}
          onClick={() => setFloatingNameEditor(null)}
        >
          <div 
            className="pup-modal"
            style={{
              ...themeStyles.floatingNameEditor,
              top: Math.min(floatingNameEditor.rect.bottom + 5, window.innerHeight - 100),
              left: Math.max(10, Math.min(floatingNameEditor.rect.left, window.innerWidth - 410))
            }}
            onClick={(e) => e.stopPropagation()}
          >
            <div style={themeStyles.floatingNameHeader}>
              <div style={themeStyles.modalTitleRow}>
                <div style={themeStyles.modalIconWrapper} aria-hidden="true">
                  <svg viewBox="0 0 24 24" style={themeStyles.modalIcon} role="presentation">
                    <path d="M3 17.25V21h3.75l11-11.003-3.75-3.75L3 17.25z" />
                    <path d="M20.71 7.04a1 1 0 0 0 0-1.414l-2.336-2.338a1 1 0 0 0-1.414 0L15.13 5.12l3.75 3.75 1.83-1.826z" />
                  </svg>
                </div>
                <span style={themeStyles.floatingNameTitle}>Rename Shape</span>
              </div>
              <button className="p-btn" 
                style={themeStyles.floatingNameClose}
                onClick={() => setFloatingNameEditor(null)}
              >
                ✕
              </button>
            </div>
            <div style={themeStyles.floatingNameContent}>
              <label style={themeStyles.floatingNameLabel}>
                Current name: {shapes[floatingNameEditor.shapeIndex]?.name}
              </label>
              <input className="p-form-text"
                type="text"
                autoFocus
                value={shapeSettings[floatingNameEditor.shapeIndex]?.customName || ''}
                placeholder={shapes[floatingNameEditor.shapeIndex]?.name}
                onChange={(e) => updateShapeSetting(floatingNameEditor.shapeIndex, 'customName', e.target.value)}
                onKeyDown={(e) => {
                  if (e.key === 'Enter' || e.key === 'Escape') {
                    setFloatingNameEditor(null);
                  }
                }}
                style={themeStyles.floatingNameInput}
              />
            </div>
          </div>
        </div>
      )}
      
      <footer style={themeStyles.footer}>
        <span>Advanced Output Toolkit</span>
      </footer>
    </div>
  );
}

// Styles matching Rekordbox converter
const styles = {
  container: { height: '100%', backgroundColor: '#0a0a0f', color: '#e0e0e8', fontFamily: "'JetBrains Mono', 'Fira Code', monospace", position: 'relative', overflow: 'auto', width: '100%' },
  gridOverlay: { position: 'fixed', top: 0, left: 0, right: 0, bottom: 0, backgroundImage: 'linear-gradient(rgba(59, 130, 246, 0.03) 1px, transparent 1px), linear-gradient(90deg, rgba(59, 130, 246, 0.03) 1px, transparent 1px)', backgroundSize: '50px 50px', pointerEvents: 'none', zIndex: 0 },
  header: { position: 'sticky', top: 0, zIndex: 100, display: 'flex', justifyContent: 'space-between', alignItems: 'center', padding: '16px 24px', borderBottom: '1px solid rgba(59, 130, 246, 0.2)', background: '#0a0a0f', backgroundImage: 'linear-gradient(180deg, rgba(59, 130, 246, 0.08) 0%, transparent 100%)' },
  logoSection: { display: 'flex', alignItems: 'baseline', gap: '16px', flexWrap: 'wrap' },
  logo: { display: 'flex', alignItems: 'center', gap: '6px', fontSize: '20px', fontWeight: '700' },
  logoText: { color: '#fff' },
  logoAccent: { color: '#3b82f6' },
  tagline: { fontSize: '10px', color: '#666' },
  headerRight: { display: 'flex', alignItems: 'center', gap: '12px' },
  themeToggleBtn: { display: 'inline-flex', alignItems: 'center', justifyContent: 'center', width: '34px', height: '34px', border: '1px solid #3b82f6', borderRadius: '8px', background: '#3b82f6', color: '#ffffff', fontSize: '16px', cursor: 'pointer', transition: 'all 0.2s', outline: 'none', boxShadow: '0 4px 12px rgba(59, 130, 246, 0.35)' },
  projectNameDisplay: { fontSize: '11px', color: '#888', maxWidth: '200px', overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' },
  versionBadge: { padding: '4px 10px', backgroundColor: 'rgba(59, 130, 246, 0.15)', color: '#3b82f6', borderRadius: '4px', fontSize: '10px', fontWeight: '600', border: '1px solid rgba(59, 130, 246, 0.3)' },
  main: { position: 'relative', zIndex: 1, maxWidth: '1200px', margin: '0 auto', padding: '24px 16px' },
  mainBase: { position: 'relative', zIndex: 1, padding: '24px 16px', boxSizing: 'border-box', width: '100%' },
  mainSideBySide: { position: 'relative', zIndex: 1, width: '100%', margin: '0', padding: '24px 16px', display: 'grid', gridTemplateColumns: 'minmax(0, 1fr) minmax(0, 1fr)', gap: '24px', boxSizing: 'border-box', alignItems: 'start' },
  sectionsColumn: { width: '100%', minWidth: 0 },
  rightColumn: { width: '100%', minWidth: 0 },
  previewColumn: { flex: '1 1 auto', minWidth: '400px', position: 'sticky', top: '24px', alignSelf: 'flex-start', maxHeight: 'calc(100vh - 120px)' },
  emptyColumnDropZone: { width: '100%', minHeight: '200px', border: '2px dashed rgba(59, 130, 246, 0.3)', borderRadius: '10px', display: 'flex', alignItems: 'center', justifyContent: 'center', background: 'rgba(59, 130, 246, 0.05)' },
  dropZoneText: { color: 'rgba(59, 130, 246, 0.5)', fontSize: '12px', textTransform: 'uppercase', letterSpacing: '1px' },
  spanningPreviewContainer: { gridColumn: '1 / -1', width: '100%' },
  columnMoveButtons: { display: 'inline-flex', gap: '2px', marginLeft: '8px' },
  columnMoveBtn: { padding: '2px 6px', backgroundColor: 'transparent', border: '1px solid rgba(255, 255, 255, 0.2)', borderRadius: '3px', color: '#666', fontSize: '8px', cursor: 'pointer', transition: 'all 0.15s', outline: 'none' },
  columnMoveBtnActive: { backgroundColor: 'rgba(59, 130, 246, 0.2)', borderColor: '#3b82f6', color: '#3b82f6' },
  columnMoveBtnInactive: { backgroundColor: 'transparent', borderColor: 'rgba(255, 255, 255, 0.2)', color: '#666' },
  section: { display: 'block', marginBottom: '4px', background: 'linear-gradient(135deg, rgba(20, 20, 30, 0.8) 0%, rgba(15, 15, 22, 0.9) 100%)', border: '1px solid rgba(255, 255, 255, 0.08)', borderRadius: '10px', padding: '16px 20px', transition: 'all 0.2s', boxSizing: 'border-box', width: '100%', overflow: 'hidden', minWidth: 0 },
  sectionCollapsed: { },
  sectionDragging: { opacity: 0.5, border: '1px dashed #3b82f6' },
  sectionHeader: { display: 'flex', alignItems: 'center', gap: '12px', fontSize: '12px', fontWeight: '600', color: '#fff', textTransform: 'uppercase', letterSpacing: '1px', cursor: 'pointer', userSelect: 'none', flexWrap: 'wrap', overflow: 'hidden', maxWidth: '100%' },
  sectionContent: { marginTop: '14px', paddingBottom: '4px', overflow: 'hidden', maxWidth: '100%' },
  sectionTitleText: { flex: '0 0 auto' },
  dragHandle: { color: '#555', cursor: 'grab', fontSize: '14px', marginRight: '-4px', padding: '4px' },
  collapseIcon: { marginLeft: 'auto', padding: '4px 8px', color: '#666', fontSize: '10px', transition: 'transform 0.2s', borderRadius: '6px' },
  sectionTitle: { display: 'flex', alignItems: 'center', gap: '12px', fontSize: '12px', fontWeight: '600', marginBottom: '14px', color: '#fff', textTransform: 'uppercase', letterSpacing: '1px' },
  enabledCounter: { fontSize: '11px', color: '#888', fontWeight: '400', textTransform: 'none', letterSpacing: '0', marginLeft: 'auto' },
  projectControls: { display: 'flex', flexWrap: 'wrap', gap: '12px', alignItems: 'flex-end' },
  projectNameInput: { display: 'flex', flexDirection: 'column', gap: '4px', minWidth: '180px' },
  projectButtons: { display: 'flex', gap: '8px', flexWrap: 'wrap' },
  viewportGroup: { display: 'flex', flexDirection: 'column', gap: '4px', marginLeft: 'auto' },
  hiddenInput: { position: 'absolute', width: '1px', height: '1px', padding: 0, margin: '-1px', overflow: 'hidden', clip: 'rect(0,0,0,0)', border: 0 },
  textInput: { padding: '10px 12px', backgroundColor: 'rgba(0, 0, 0, 0.4)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '5px', color: '#fff', fontSize: '12px', fontFamily: 'inherit' },
  numberInput: { padding: '10px 12px', backgroundColor: 'rgba(0, 0, 0, 0.4)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '5px', color: '#fff', fontSize: '12px', fontFamily: 'inherit', width: '80px' },
  label: { fontSize: '9px', color: '#888', textTransform: 'uppercase', letterSpacing: '1px' },
  importButtonLabel: { display: 'inline-flex', alignItems: 'center', justifyContent: 'center', gap: '6px', padding: '12px 16px', width: '100%', minHeight: '44px', backgroundColor: 'rgba(59, 130, 246, 0.15)', color: '#3b82f6', border: '1px solid #3b82f6', borderRadius: '5px', cursor: 'pointer', fontSize: '11px', fontWeight: '600', textAlign: 'center', transition: 'all 0.2s', outline: 'none' },
  importRow: { display: 'grid', gridTemplateColumns: 'repeat(auto-fit, minmax(220px, 1fr))', gap: '14px 18px', alignItems: 'stretch', width: '100%', maxWidth: '100%', overflow: 'hidden' },
  importGroup: { display: 'grid', gridTemplateRows: 'auto auto', alignContent: 'start', gap: '10px', minWidth: '200px' },
  inlineInputGroup: { display: 'flex', alignItems: 'center', gap: '8px' },
  inlineLabel: { fontSize: '11px', color: '#888', textTransform: 'uppercase', letterSpacing: '0.5px' },
  openButton: { display: 'inline-flex', alignItems: 'center', gap: '6px', padding: '10px 16px', backgroundColor: 'rgba(255, 255, 255, 0.08)', color: '#e0e0e8', border: '1px solid rgba(255, 255, 255, 0.2)', borderRadius: '5px', cursor: 'pointer', fontSize: '11px', fontWeight: '500', transition: 'all 0.2s', outline: 'none' },
  saveButton: { display: 'inline-flex', alignItems: 'center', gap: '6px', padding: '10px 16px', backgroundColor: 'rgba(59, 130, 246, 0.15)', color: '#3b82f6', border: '1px solid rgba(59, 130, 246, 0.5)', borderRadius: '5px', cursor: 'pointer', fontSize: '11px', fontWeight: '600', transition: 'all 0.2s', outline: 'none' },
  buttonDisabled: { opacity: 0.4, cursor: 'not-allowed' },
  trackCount: { color: '#3b82f6', fontSize: '11px', fontWeight: '500', marginLeft: '12px' },
  presetRow: { display: 'flex', flexWrap: 'wrap', gap: '8px', marginBottom: '16px', overflow: 'hidden', maxWidth: '100%' },
  presetButton: { padding: '10px 14px', backgroundColor: 'rgba(255, 255, 255, 0.08)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '5px', color: '#ccc', fontSize: '11px', cursor: 'pointer', transition: 'all 0.15s', outline: 'none' },
  presetButtonActive: { backgroundColor: 'rgba(59, 130, 246, 0.2)', border: '1px solid #3b82f6', color: '#3b82f6' },
  presetButtonInactive: { backgroundColor: 'rgba(255, 255, 255, 0.08)', borderColor: 'rgba(255, 255, 255, 0.15)', color: '#ccc' },
  buttonGroup: { display: 'flex', gap: '4px', flexWrap: 'wrap' },
  toggleButton: { padding: '6px 12px', backgroundColor: 'rgba(255, 255, 255, 0.08)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '4px', color: '#ccc', fontSize: '11px', cursor: 'pointer', transition: 'all 0.15s', outline: 'none' },
  toggleButtonActive: { backgroundColor: 'rgba(59, 130, 246, 0.2)', borderColor: '#3b82f6', color: '#3b82f6' },
  toggleButtonInactive: { backgroundColor: 'rgba(255, 255, 255, 0.08)', borderColor: 'rgba(255, 255, 255, 0.15)', color: '#ccc' },
  scaleToFitButton: { padding: '10px 14px', backgroundColor: 'rgba(255, 255, 255, 0.08)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '5px', color: '#ccc', fontSize: '12px', cursor: 'pointer', transition: 'all 0.15s', fontFamily: 'inherit', whiteSpace: 'nowrap', outline: 'none' },
  scaleToFitButtonActive: { backgroundColor: 'rgba(59, 130, 246, 0.2)', borderColor: '#3b82f6', color: '#3b82f6' },
  scaleToFitButtonInactive: { backgroundColor: 'rgba(255, 255, 255, 0.08)', borderColor: 'rgba(255, 255, 255, 0.15)', color: '#ccc' },
  inputRow: { display: 'flex', flexWrap: 'wrap', gap: '16px', overflow: 'hidden', maxWidth: '100%' },
  inputGroup: { display: 'flex', flexDirection: 'column', gap: '4px' },
  screensContainer: { display: 'flex', flexDirection: 'column', gap: '8px', marginBottom: '12px', maxWidth: '100%', overflow: 'hidden' },
  screenItem: { display: 'flex', alignItems: 'center', gap: '8px', padding: '10px 12px', backgroundColor: 'rgba(0, 0, 0, 0.3)', borderRadius: '6px', border: '1px solid rgba(255, 255, 255, 0.08)', flexWrap: 'wrap', maxWidth: '100%' },
  screenNameInput: { flex: 1, padding: '6px 10px', backgroundColor: 'rgba(0, 0, 0, 0.4)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '4px', color: '#fff', fontSize: '11px', fontFamily: 'inherit', minWidth: '100px' },
  screenSizeInput: { width: '70px', padding: '6px 8px', backgroundColor: 'rgba(0, 0, 0, 0.4)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '4px', color: '#fff', fontSize: '11px', fontFamily: 'inherit', textAlign: 'center' },
  screenSizeX: { color: '#666', fontSize: '11px' },
  screenResetBtn: { padding: '4px 8px', backgroundColor: 'transparent', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '4px', color: '#888', fontSize: '11px', cursor: 'pointer', outline: 'none' },
  screenRemoveBtn: { padding: '4px 8px', backgroundColor: 'rgba(255, 80, 80, 0.1)', border: '1px solid rgba(255, 80, 80, 0.3)', borderRadius: '4px', color: '#ff6b6b', fontSize: '11px', cursor: 'pointer', outline: 'none' },
  screenShapeCount: { fontSize: '10px', color: '#666', marginLeft: 'auto' },
  addScreenBtn: { padding: '8px 16px', backgroundColor: 'rgba(59, 130, 246, 0.15)', border: '1px solid rgba(59, 130, 246, 0.5)', borderRadius: '5px', color: '#3b82f6', fontSize: '11px', fontWeight: '600', cursor: 'pointer', outline: 'none' },
  shapesToolbar: { display: 'flex', flexWrap: 'wrap', gap: '12px', alignItems: 'flex-end', marginBottom: '12px' },
  outputTypeGroup: { display: 'flex', flexDirection: 'column', gap: '4px' },
  outputTypeButtons: { display: 'flex', gap: '4px', flexWrap: 'wrap' },
  outputTypeBtn: { padding: '6px 12px', backgroundColor: 'rgba(255, 255, 255, 0.08)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '4px', color: '#ccc', fontSize: '10px', cursor: 'pointer', outline: 'none' },
  outputTypeBtnActive: { backgroundColor: 'rgba(59, 130, 246, 0.2)', borderColor: '#3b82f6', color: '#3b82f6' },
  outputTypeBtnInactive: { backgroundColor: 'rgba(255, 255, 255, 0.08)', borderColor: 'rgba(255, 255, 255, 0.15)', color: '#ccc' },
  applyAllBtn: { padding: '6px 12px', backgroundColor: 'rgba(255, 255, 255, 0.08)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '4px', color: '#ccc', fontSize: '10px', fontWeight: '600', cursor: 'pointer', outline: 'none' },
  toggleBtn: { padding: '6px 12px', backgroundColor: 'rgba(255, 255, 255, 0.08)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '4px', color: '#ccc', fontSize: '10px', cursor: 'pointer', outline: 'none' },
  shapesTable: { border: '1px solid rgba(255, 255, 255, 0.1)', borderRadius: '6px', overflow: 'hidden' },
  shapesTableHeader: { display: 'flex', alignItems: 'center', gap: '8px', padding: '10px 12px', backgroundColor: 'rgba(255, 255, 255, 0.05)', fontSize: '9px', fontWeight: '700', textTransform: 'uppercase', letterSpacing: '1px', color: '#888' },
  shapesTableBody: { maxHeight: '250px', overflowY: 'auto' },
  shapeRow: { display: 'flex', alignItems: 'center', gap: '8px', padding: '8px 12px', borderBottom: '1px solid rgba(255, 255, 255, 0.05)', transition: 'background-color 0.1s' },
  shapeRowDisabled: { backgroundColor: 'rgba(0, 0, 0, 0.2)' },
  shapeName: { flex: 1, fontSize: '11px', color: '#fff', fontWeight: '500', overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' },
  shapeNameInput: { width: '100%', padding: '4px 8px', backgroundColor: 'rgba(0, 0, 0, 0.4)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '4px', color: '#fff', fontSize: '11px', fontFamily: 'inherit' },
  floatingNameOverlay: { position: 'fixed', top: 0, left: 0, right: 0, bottom: 0, backgroundColor: 'rgba(0, 0, 0, 0.5)', zIndex: 1000 },
  floatingNameEditor: { position: 'fixed', width: '400px', backgroundColor: 'rgba(20, 20, 30, 0.98)', border: '1px solid rgba(59, 130, 246, 0.4)', borderRadius: '8px', boxShadow: '0 8px 32px rgba(0, 0, 0, 0.5)', zIndex: 1001 },
  floatingNameHeader: { display: 'flex', justifyContent: 'space-between', alignItems: 'center', padding: '12px 16px', borderBottom: '1px solid rgba(255, 255, 255, 0.1)' },
  modalTitleRow: { display: 'flex', alignItems: 'center', gap: '10px', minWidth: 0 },
  modalIconWrapper: { width: '36px', height: '36px', borderRadius: '10px', backgroundColor: 'rgba(59, 130, 246, 0.12)', border: '1px solid rgba(59, 130, 246, 0.4)', display: 'inline-flex', alignItems: 'center', justifyContent: 'center', color: '#3b82f6', flexShrink: 0 },
  modalIcon: { width: '18px', height: '18px', fill: 'currentColor' },
  floatingNameTitle: { color: '#3b82f6', fontSize: '13px', fontWeight: '600' },
  floatingNameClose: { background: 'none', border: 'none', color: '#888', fontSize: '16px', cursor: 'pointer', padding: '4px 8px', borderRadius: '4px', transition: 'all 0.15s' },
  floatingNameContent: { padding: '16px' },
  floatingNameLabel: { display: 'block', color: '#888', fontSize: '11px', marginBottom: '8px', overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' },
  floatingNameInput: { width: '100%', padding: '10px 12px', backgroundColor: 'rgba(0, 0, 0, 0.4)', border: '1px solid rgba(255, 255, 255, 0.2)', borderRadius: '6px', color: '#fff', fontSize: '14px', fontFamily: 'inherit', outline: 'none', boxSizing: 'border-box' },
  checkbox: { width: '14px', height: '14px', cursor: 'pointer', accentColor: '#3b82f6' },
  screenSelect: { padding: '4px 8px', backgroundColor: 'rgba(0, 0, 0, 0.4)', border: '1px solid rgba(255, 255, 255, 0.15)', borderRadius: '4px', color: '#fff', fontSize: '10px', fontFamily: 'inherit' },
  pointCount: { width: '50px', textAlign: 'right', fontSize: '10px', color: '#666' },
  shapeSummary: { padding: '10px 12px', fontSize: '11px', color: '#888', borderTop: '1px solid rgba(255, 255, 255, 0.08)', marginTop: '8px' },
  emptyShapesState: { display: 'flex', flexDirection: 'column', alignItems: 'center', justifyContent: 'center', padding: '40px 20px', color: '#666' },
  emptyShapesText: { fontSize: '14px', color: '#888', marginBottom: '4px' },
  emptyShapesHint: { fontSize: '11px', color: '#555' },
  exportRow: { display: 'flex', alignItems: 'center', gap: '12px', marginBottom: '16px', flexWrap: 'wrap' },
  checkboxLabel: { display: 'flex', alignItems: 'center', gap: '8px', cursor: 'pointer', fontSize: '12px', color: '#fff' },
  checkboxHint: { fontSize: '10px', color: '#666' },
  inputHint: { fontSize: '9px', color: '#666', marginTop: '2px' },
  generateButton: { padding: '12px 24px', backgroundColor: '#3b82f6', color: '#000', border: 'none', borderRadius: '5px', fontSize: '12px', fontWeight: '700', cursor: 'pointer', transition: 'all 0.15s', outline: 'none' },
  arenaExportButton: { padding: '14px 24px', backgroundColor: '#2B5244', color: '#85FED3', border: '2px solid #85FED3', borderRadius: '8px', fontSize: '12px', fontWeight: '800', letterSpacing: '0.3px', cursor: 'pointer', transition: 'transform 0.12s ease, box-shadow 0.12s ease', outline: 'none', boxShadow: '0 6px 14px rgba(43, 82, 68, 0.35)' },
  arenaExportButtonHover: { transform: 'translateY(-1px)', boxShadow: '0 10px 22px rgba(43, 82, 68, 0.55)' },
  previewContainer: { position: 'relative', backgroundColor: '#000', borderRadius: '0', overflow: 'visible', margin: '0 auto' },
  previewSvg: { display: 'block' },
  previewPlaceholder: { position: 'absolute', inset: 0, display: 'flex', alignItems: 'center', justifyContent: 'center', color: '#666', fontSize: '12px', padding: '10px 10px 30px 10px', textAlign: 'center', pointerEvents: 'none' },
  previewLegend: { position: 'absolute', top: '12px', left: '12px', backgroundColor: 'rgba(0, 0, 0, 0.7)', padding: '12px 14px', borderRadius: '6px', display: 'flex', flexDirection: 'column', gap: '8px', pointerEvents: 'none' },
  legendItem: { display: 'flex', alignItems: 'center', gap: '10px', fontSize: '14px' },
  legendDot: { width: '16px', height: '16px', borderRadius: '3px' },
  sectionIconWrapper: { width: '32px', height: '32px', borderRadius: '9px', backgroundColor: 'rgba(59, 130, 246, 0.12)', border: '1px solid rgba(59, 130, 246, 0.35)', display: 'inline-flex', alignItems: 'center', justifyContent: 'center', color: '#3b82f6', flexShrink: 0, verticalAlign: 'middle', lineHeight: 1 },
  sectionIcon: { width: '18px', height: '18px', fill: 'currentColor' },
  previewSize: { position: 'absolute', bottom: '8px', right: '8px', backgroundColor: 'rgba(0, 0, 0, 0.7)', padding: '4px 8px', borderRadius: '4px', fontSize: '10px', color: '#888', pointerEvents: 'none' },
  previewToolbar: { display: 'flex', alignItems: 'center', gap: '6px', marginLeft: 'auto' },
  previewToolbarButton: { width: '35px', height: '35px', display: 'flex', alignItems: 'center', justifyContent: 'center', backgroundColor: 'rgba(255, 255, 255, 0.08)', border: '2px solid rgba(255, 255, 255, 0.15)', borderRadius: '5px', color: '#ccc', fontSize: '18px', cursor: 'pointer', transition: 'all 0.15s', fontFamily: 'inherit', outline: 'none' },
  previewToolbarButtonActive: { backgroundColor: 'rgba(59, 130, 246, 0.2)', borderColor: '#3b82f6', color: '#3b82f6' },
  previewToolbarButtonInactive: { backgroundColor: 'rgba(255, 255, 255, 0.08)', borderColor: 'rgba(255, 255, 255, 0.15)', color: '#ccc' },
  previewToolbarDivider: { width: '2px', height: '26px', backgroundColor: 'rgba(255, 255, 255, 0.15)', margin: '0 5px' },
  previewZoomLevel: { fontSize: '13px', color: '#888', minWidth: '50px', textAlign: 'center' },
  shapeRowSelected: { backgroundColor: 'rgba(255, 149, 0, 0.15)', borderLeft: '2px solid #ff9500' },
  footer: { position: 'relative', zIndex: 1, display: 'flex', justifyContent: 'center', alignItems: 'center', gap: '10px', padding: '2px 8px 10px 8px', fontSize: '10px', color: '#555', borderTop: '1px solid rgba(255, 255, 255, 0.05)' },
  footerDot: { color: '#3b82f6' },
};

// Light theme overrides
const lightThemeOverrides = {
  container: { height: '100%', backgroundColor: '#f5f5f7', color: '#1d1d1f', fontFamily: "'JetBrains Mono', 'Fira Code', monospace", position: 'relative', overflow: 'auto', width: '100%' },
  gridOverlay: { position: 'fixed', top: 0, left: 0, right: 0, bottom: 0, backgroundImage: 'linear-gradient(rgba(59, 130, 246, 0.04) 1px, transparent 1px), linear-gradient(90deg, rgba(59, 130, 246, 0.04) 1px, transparent 1px)', backgroundSize: '50px 50px', pointerEvents: 'none', zIndex: 0 },
  header: { position: 'sticky', top: 0, zIndex: 100, display: 'flex', justifyContent: 'space-between', alignItems: 'center', padding: '16px 24px', borderBottom: '1px solid rgba(59, 130, 246, 0.25)', background: '#f5f5f7', backgroundImage: 'linear-gradient(180deg, rgba(59, 130, 246, 0.1) 0%, transparent 100%)' },
  logoText: { color: '#1d1d1f' },
  tagline: { fontSize: '10px', color: '#86868b' },
  projectNameDisplay: { fontSize: '11px', color: '#86868b', maxWidth: '200px', overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' },
  versionBadge: { padding: '4px 10px', backgroundColor: 'rgba(59, 130, 246, 0.15)', color: '#2563eb', borderRadius: '4px', fontSize: '10px', fontWeight: '600', border: '1px solid rgba(59, 130, 246, 0.4)' },
  section: { display: 'block', marginBottom: '4px', background: 'linear-gradient(135deg, rgba(255, 255, 255, 0.95) 0%, rgba(250, 250, 252, 0.98) 100%)', border: '1px solid rgba(0, 0, 0, 0.08)', borderRadius: '10px', padding: '16px 20px', transition: 'all 0.2s', boxSizing: 'border-box', width: '100%', overflow: 'hidden', minWidth: 0, boxShadow: '0 1px 3px rgba(0, 0, 0, 0.04)' },
  sectionDragging: { opacity: 0.5, border: '1px dashed #3b82f6' },
  sectionHeader: { display: 'flex', alignItems: 'center', gap: '12px', fontSize: '12px', fontWeight: '600', color: '#1d1d1f', textTransform: 'uppercase', letterSpacing: '1px', cursor: 'pointer', userSelect: 'none', flexWrap: 'wrap', overflow: 'hidden', maxWidth: '100%' },
  dragHandle: { color: '#aeaeb2', cursor: 'grab', fontSize: '14px', marginRight: '-4px', padding: '4px' },
  collapseIcon: { marginLeft: 'auto', padding: '4px 8px', color: '#86868b', fontSize: '10px', transition: 'transform 0.2s', borderRadius: '6px' },
  sectionTitle: { display: 'flex', alignItems: 'center', gap: '12px', fontSize: '12px', fontWeight: '600', marginBottom: '14px', color: '#1d1d1f', textTransform: 'uppercase', letterSpacing: '1px' },
  enabledCounter: { fontSize: '11px', color: '#86868b', fontWeight: '400', textTransform: 'none', letterSpacing: '0', marginLeft: 'auto' },
  columnMoveBtn: { padding: '2px 6px', backgroundColor: 'transparent', border: '1px solid rgba(0, 0, 0, 0.15)', borderRadius: '3px', color: '#86868b', fontSize: '8px', cursor: 'pointer', transition: 'all 0.15s', outline: 'none' },
  columnMoveBtnInactive: { backgroundColor: 'transparent', borderColor: 'rgba(0, 0, 0, 0.15)', color: '#86868b' },
  emptyColumnDropZone: { width: '100%', minHeight: '200px', border: '2px dashed rgba(59, 130, 246, 0.4)', borderRadius: '10px', display: 'flex', alignItems: 'center', justifyContent: 'center', background: 'rgba(59, 130, 246, 0.05)' },
  dropZoneText: { color: 'rgba(59, 130, 246, 0.6)', fontSize: '12px', textTransform: 'uppercase', letterSpacing: '1px' },
  textInput: { padding: '10px 12px', backgroundColor: 'rgba(255, 255, 255, 0.9)', border: '1px solid rgba(0, 0, 0, 0.12)', borderRadius: '5px', color: '#1d1d1f', fontSize: '12px', fontFamily: 'inherit' },
  numberInput: { padding: '10px 12px', backgroundColor: 'rgba(255, 255, 255, 0.9)', border: '1px solid rgba(0, 0, 0, 0.12)', borderRadius: '5px', color: '#1d1d1f', fontSize: '12px', fontFamily: 'inherit', width: '80px' },
  label: { fontSize: '9px', color: '#86868b', textTransform: 'uppercase', letterSpacing: '1px' },
  importButtonLabel: { display: 'inline-flex', alignItems: 'center', justifyContent: 'center', gap: '6px', padding: '12px 16px', width: '100%', minHeight: '44px', backgroundColor: 'rgba(59, 130, 246, 0.12)', color: '#2563eb', border: '1px solid rgba(59, 130, 246, 0.5)', borderRadius: '5px', cursor: 'pointer', fontSize: '11px', fontWeight: '600', textAlign: 'center', transition: 'all 0.2s', outline: 'none' },
  inlineLabel: { fontSize: '11px', color: '#86868b', textTransform: 'uppercase', letterSpacing: '0.5px' },
  openButton: { display: 'inline-flex', alignItems: 'center', gap: '6px', padding: '10px 16px', backgroundColor: 'rgba(0, 0, 0, 0.04)', color: '#1d1d1f', border: '1px solid rgba(0, 0, 0, 0.12)', borderRadius: '5px', cursor: 'pointer', fontSize: '11px', fontWeight: '500', transition: 'all 0.2s', outline: 'none' },
  saveButton: { display: 'inline-flex', alignItems: 'center', gap: '6px', padding: '10px 16px', backgroundColor: 'rgba(59, 130, 246, 0.12)', color: '#2563eb', border: '1px solid rgba(59, 130, 246, 0.4)', borderRadius: '5px', cursor: 'pointer', fontSize: '11px', fontWeight: '600', transition: 'all 0.2s', outline: 'none' },
  trackCount: { color: '#2563eb', fontSize: '11px', fontWeight: '500', marginLeft: '12px' },
  presetButton: { padding: '10px 14px', backgroundColor: 'rgba(0, 0, 0, 0.04)', border: '1px solid rgba(0, 0, 0, 0.1)', borderRadius: '5px', color: '#1d1d1f', fontSize: '11px', cursor: 'pointer', transition: 'all 0.15s', outline: 'none' },
  presetButtonActive: { backgroundColor: 'rgba(59, 130, 246, 0.15)', border: '1px solid #3b82f6', color: '#2563eb' },
  presetButtonInactive: { backgroundColor: 'rgba(0, 0, 0, 0.04)', borderColor: 'rgba(0, 0, 0, 0.1)', color: '#1d1d1f' },
  toggleButton: { padding: '6px 12px', backgroundColor: 'rgba(0, 0, 0, 0.04)', border: '1px solid rgba(0, 0, 0, 0.1)', borderRadius: '4px', color: '#1d1d1f', fontSize: '11px', cursor: 'pointer', transition: 'all 0.15s', outline: 'none' },
  toggleButtonActive: { backgroundColor: 'rgba(59, 130, 246, 0.15)', borderColor: '#3b82f6', color: '#2563eb' },
  toggleButtonInactive: { backgroundColor: 'rgba(0, 0, 0, 0.04)', borderColor: 'rgba(0, 0, 0, 0.1)', color: '#1d1d1f' },
  scaleToFitButton: { padding: '10px 14px', backgroundColor: 'rgba(0, 0, 0, 0.04)', border: '1px solid rgba(0, 0, 0, 0.1)', borderRadius: '5px', color: '#1d1d1f', fontSize: '12px', cursor: 'pointer', transition: 'all 0.15s', fontFamily: 'inherit', whiteSpace: 'nowrap', outline: 'none' },
  scaleToFitButtonActive: { backgroundColor: 'rgba(59, 130, 246, 0.15)', borderColor: '#3b82f6', color: '#2563eb' },
  scaleToFitButtonInactive: { backgroundColor: 'rgba(0, 0, 0, 0.04)', borderColor: 'rgba(0, 0, 0, 0.1)', color: '#1d1d1f' },
  screenItem: { display: 'flex', alignItems: 'center', gap: '8px', padding: '10px 12px', backgroundColor: 'rgba(0, 0, 0, 0.02)', borderRadius: '6px', border: '1px solid rgba(0, 0, 0, 0.06)', flexWrap: 'wrap', maxWidth: '100%' },
  screenNameInput: { flex: 1, padding: '6px 10px', backgroundColor: 'rgba(255, 255, 255, 0.9)', border: '1px solid rgba(0, 0, 0, 0.12)', borderRadius: '4px', color: '#1d1d1f', fontSize: '11px', fontFamily: 'inherit', minWidth: '100px' },
  screenSizeInput: { width: '70px', padding: '6px 8px', backgroundColor: 'rgba(255, 255, 255, 0.9)', border: '1px solid rgba(0, 0, 0, 0.12)', borderRadius: '4px', color: '#1d1d1f', fontSize: '11px', fontFamily: 'inherit', textAlign: 'center' },
  screenSizeX: { color: '#86868b', fontSize: '11px' },
  screenResetBtn: { padding: '4px 8px', backgroundColor: 'transparent', border: '1px solid rgba(0, 0, 0, 0.12)', borderRadius: '4px', color: '#86868b', fontSize: '11px', cursor: 'pointer', outline: 'none' },
  screenRemoveBtn: { padding: '4px 8px', backgroundColor: 'rgba(255, 59, 48, 0.08)', border: '1px solid rgba(255, 59, 48, 0.3)', borderRadius: '4px', color: '#ff3b30', fontSize: '11px', cursor: 'pointer', outline: 'none' },
  screenShapeCount: { fontSize: '10px', color: '#86868b', marginLeft: 'auto' },
  addScreenBtn: { padding: '8px 16px', backgroundColor: 'rgba(59, 130, 246, 0.12)', border: '1px solid rgba(59, 130, 246, 0.4)', borderRadius: '5px', color: '#2563eb', fontSize: '11px', fontWeight: '600', cursor: 'pointer', outline: 'none' },
  outputTypeBtn: { padding: '6px 12px', backgroundColor: 'rgba(0, 0, 0, 0.04)', border: '1px solid rgba(0, 0, 0, 0.1)', borderRadius: '4px', color: '#1d1d1f', fontSize: '10px', cursor: 'pointer', outline: 'none' },
  outputTypeBtnActive: { backgroundColor: 'rgba(59, 130, 246, 0.15)', borderColor: '#3b82f6', color: '#2563eb' },
  outputTypeBtnInactive: { backgroundColor: 'rgba(0, 0, 0, 0.04)', borderColor: 'rgba(0, 0, 0, 0.1)', color: '#1d1d1f' },
  applyAllBtn: { padding: '6px 12px', backgroundColor: 'rgba(0, 0, 0, 0.04)', border: '1px solid rgba(0, 0, 0, 0.1)', borderRadius: '4px', color: '#1d1d1f', fontSize: '10px', fontWeight: '600', cursor: 'pointer', outline: 'none' },
  toggleBtn: { padding: '6px 12px', backgroundColor: 'rgba(0, 0, 0, 0.04)', border: '1px solid rgba(0, 0, 0, 0.1)', borderRadius: '4px', color: '#1d1d1f', fontSize: '10px', cursor: 'pointer', outline: 'none' },
  shapesTable: { border: '1px solid rgba(0, 0, 0, 0.08)', borderRadius: '6px', overflow: 'hidden' },
  shapesTableHeader: { display: 'flex', alignItems: 'center', gap: '8px', padding: '10px 12px', backgroundColor: 'rgba(0, 0, 0, 0.03)', fontSize: '9px', fontWeight: '700', textTransform: 'uppercase', letterSpacing: '1px', color: '#86868b' },
  shapeRow: { display: 'flex', alignItems: 'center', gap: '8px', padding: '8px 12px', borderTop: '1px solid rgba(0, 0, 0, 0.06)', fontSize: '11px', cursor: 'pointer', transition: 'background-color 0.15s' },
  shapeRowDisabled: { backgroundColor: 'rgba(0, 0, 0, 0.02)' },
  shapeName: { flex: 1, fontSize: '11px', color: '#1d1d1f', fontWeight: '500', overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' },
  shapeNameInput: { width: '100%', padding: '4px 8px', backgroundColor: 'rgba(255, 255, 255, 0.9)', border: '1px solid rgba(0, 0, 0, 0.12)', borderRadius: '4px', color: '#1d1d1f', fontSize: '11px', fontFamily: 'inherit' },
  floatingNameOverlay: { position: 'fixed', top: 0, left: 0, right: 0, bottom: 0, backgroundColor: 'rgba(0, 0, 0, 0.3)', zIndex: 1000 },
  floatingNameEditor: { position: 'fixed', width: '400px', backgroundColor: 'rgba(255, 255, 255, 0.98)', border: '1px solid rgba(59, 130, 246, 0.4)', borderRadius: '8px', boxShadow: '0 8px 32px rgba(0, 0, 0, 0.15)', zIndex: 1001 },
  modalTitleRow: { display: 'flex', alignItems: 'center', gap: '10px', minWidth: 0 },
  modalIconWrapper: { width: '36px', height: '36px', borderRadius: '10px', backgroundColor: 'rgba(37, 99, 235, 0.12)', border: '1px solid rgba(37, 99, 235, 0.35)', display: 'inline-flex', alignItems: 'center', justifyContent: 'center', color: '#2563eb', flexShrink: 0, verticalAlign: 'middle', lineHeight: 1 },
  modalIcon: { width: '18px', height: '18px', fill: 'currentColor' },
  floatingNameTitle: { color: '#2563eb', fontSize: '13px', fontWeight: '600' },
  floatingNameClose: { background: 'none', border: 'none', color: '#86868b', fontSize: '16px', cursor: 'pointer', padding: '4px 8px', borderRadius: '4px', transition: 'all 0.15s' },
  floatingNameLabel: { display: 'block', color: '#86868b', fontSize: '11px', marginBottom: '8px', overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' },
  floatingNameInput: { width: '100%', padding: '10px 12px', backgroundColor: 'rgba(255, 255, 255, 0.9)', border: '1px solid rgba(0, 0, 0, 0.15)', borderRadius: '6px', color: '#1d1d1f', fontSize: '14px', fontFamily: 'inherit', outline: 'none', boxSizing: 'border-box' },
  screenSelect: { padding: '4px 8px', backgroundColor: 'rgba(255, 255, 255, 0.9)', border: '1px solid rgba(0, 0, 0, 0.12)', borderRadius: '4px', color: '#1d1d1f', fontSize: '10px', fontFamily: 'inherit' },
  pointCount: { width: '50px', textAlign: 'right', fontSize: '10px', color: '#86868b' },
  shapeSummary: { padding: '10px 12px', fontSize: '11px', color: '#86868b', borderTop: '1px solid rgba(0, 0, 0, 0.06)', marginTop: '8px' },
  emptyShapesState: { display: 'flex', flexDirection: 'column', alignItems: 'center', justifyContent: 'center', padding: '40px 20px', color: '#86868b' },
  emptyShapesText: { fontSize: '14px', color: '#86868b', marginBottom: '4px' },
  emptyShapesHint: { fontSize: '11px', color: '#aeaeb2' },
  checkboxLabel: { display: 'flex', alignItems: 'center', gap: '8px', cursor: 'pointer', fontSize: '12px', color: '#1d1d1f' },
  checkboxHint: { fontSize: '10px', color: '#86868b' },
  inputHint: { fontSize: '9px', color: '#86868b', marginTop: '2px' },
  generateButton: { padding: '12px 24px', backgroundColor: '#3b82f6', color: '#000', border: 'none', borderRadius: '5px', fontSize: '12px', fontWeight: '700', cursor: 'pointer', transition: 'all 0.15s', outline: 'none' },
  previewToolbarButton: { width: '35px', height: '35px', display: 'flex', alignItems: 'center', justifyContent: 'center', backgroundColor: 'rgba(0, 0, 0, 0.06)', border: '2px solid rgba(0, 0, 0, 0.1)', borderRadius: '5px', color: '#1d1d1f', fontSize: '18px', cursor: 'pointer', transition: 'all 0.15s', fontFamily: 'inherit', outline: 'none' },
  previewToolbarButtonActive: { backgroundColor: 'rgba(59, 130, 246, 0.2)', borderColor: '#3b82f6', color: '#2563eb' },
  previewToolbarButtonInactive: { backgroundColor: 'rgba(0, 0, 0, 0.06)', borderColor: 'rgba(0, 0, 0, 0.1)', color: '#1d1d1f' },
  previewToolbarDivider: { width: '2px', height: '26px', backgroundColor: 'rgba(0, 0, 0, 0.1)', margin: '0 5px' },
  previewZoomLevel: { fontSize: '13px', color: '#86868b', minWidth: '50px', textAlign: 'center' },
  shapeRowSelected: { backgroundColor: 'rgba(255, 149, 0, 0.12)', borderLeft: '2px solid #ff9500' },
  footer: { position: 'relative', zIndex: 1, display: 'flex', justifyContent: 'center', alignItems: 'center', gap: '10px', padding: '2px 8px 10px 8px', fontSize: '10px', color: '#86868b', borderTop: '1px solid rgba(0, 0, 0, 0.06)' },
};

// Apply Puppertino palette on top of existing inline styles without altering layout values
function getThemedStyles(theme) {
  const themed = { ...(theme === 'light' ? { ...styles, ...lightThemeOverrides } : styles) };
  const panelBg = theme === 'light' ? 'var(--panel-surface)' : 'var(--panel-surface)';
  const panelText = 'var(--panel-text)';
  const panelBorder = '1px solid var(--panel-border)';
  const muted = 'var(--panel-muted)';
  const accent = 'var(--accent)';

  // Core surfaces
  themed.container = { ...themed.container, backgroundColor: panelBg, color: panelText, fontFamily: "-apple-system, BlinkMacSystemFont, 'SF Pro Text', 'Inter', 'Segoe UI', sans-serif" };
  themed.header = { ...themed.header, background: 'var(--panel-surface-2)', borderBottom: panelBorder };
  themed.section = { ...themed.section, background: panelBg, border: panelBorder };
  themed.sectionHeader = { ...themed.sectionHeader, color: panelText };
  themed.sectionTitle = { ...themed.sectionTitle, color: panelText };
  themed.tagline = { ...themed.tagline, color: muted };
  themed.collapseIcon = { ...themed.collapseIcon, color: muted };
  themed.enabledCounter = { ...themed.enabledCounter, color: muted };
  themed.sectionContent = { ...themed.sectionContent, color: panelText };
  themed.logoText = { ...themed.logoText, color: panelText };
  themed.logoAccent = { ...themed.logoAccent, color: accent };
  themed.versionBadge = { ...themed.versionBadge, backgroundColor: 'var(--accent-weak)', border: panelBorder, color: accent };
  themed.projectNameDisplay = { ...themed.projectNameDisplay, color: muted };

  // Inputs
  themed.textInput = { ...themed.textInput, backgroundColor: 'var(--surface-elevated)', border: panelBorder, color: panelText };
  themed.numberInput = { ...themed.numberInput, backgroundColor: 'var(--surface-elevated)', border: panelBorder, color: panelText };
  themed.screenNameInput = { ...themed.screenNameInput, backgroundColor: 'var(--surface-elevated)', border: panelBorder, color: panelText };
  themed.screenSizeInput = { ...themed.screenSizeInput, backgroundColor: 'var(--surface-elevated)', border: panelBorder, color: panelText };
  themed.screenSelect = { ...themed.screenSelect, backgroundColor: 'var(--surface-elevated)', border: panelBorder, color: panelText };
  themed.shapeNameInput = { ...themed.shapeNameInput, backgroundColor: 'var(--surface-elevated)', border: panelBorder, color: panelText };
  themed.floatingNameInput = { ...themed.floatingNameInput, backgroundColor: 'var(--surface-elevated)', border: panelBorder, color: panelText };

  // Buttons (remove old colors so Puppertino classes take over)
  const buttonKeys = [
    'importButtonLabel','openButton','saveButton','presetButton','presetButtonActive','presetButtonInactive','toggleButton','toggleButtonActive','toggleButtonInactive','scaleToFitButton','scaleToFitButtonActive','scaleToFitButtonInactive','addScreenBtn','outputTypeBtn','outputTypeBtnActive','outputTypeBtnInactive','applyAllBtn','toggleBtn','previewToolbarButton','previewToolbarButtonActive','previewToolbarButtonInactive','generateButton','screenRemoveBtn','screenResetBtn','columnMoveBtn','columnMoveBtnActive','columnMoveBtnInactive','shapeRow','shapeRowSelected','shapeRowDisabled'
  ];
  buttonKeys.forEach(key => {
    if (!themed[key]) return;
    const clone = { ...themed[key] };
    delete clone.backgroundColor;
    delete clone.border;
    delete clone.borderColor;
    delete clone.color;
    themed[key] = clone;
  });

  // Stateful button treatments (preserve active/inactive feedback)
  const ghost = 'var(--surface-elevated)';
  themed.presetButtonActive = { ...themed.presetButtonActive, backgroundColor: accent, color: '#fff', border: `1px solid ${accent}` };
  themed.presetButtonInactive = { ...themed.presetButtonInactive, backgroundColor: ghost, color: panelText, border: panelBorder };

  themed.toggleButtonActive = { ...themed.toggleButtonActive, backgroundColor: 'var(--accent-weak)', color: accent, border: `1px solid ${accent}` };
  themed.toggleButtonInactive = { ...themed.toggleButtonInactive, backgroundColor: ghost, color: panelText, border: panelBorder };

  themed.scaleToFitButtonActive = { ...themed.scaleToFitButtonActive, backgroundColor: 'var(--accent-weak)', color: accent, border: `1px solid ${accent}` };
  themed.scaleToFitButtonInactive = { ...themed.scaleToFitButtonInactive, backgroundColor: ghost, color: panelText, border: panelBorder };

  themed.outputTypeBtnActive = { ...themed.outputTypeBtnActive, backgroundColor: 'var(--accent-weak)', color: accent, border: `1px solid ${accent}` };
  themed.outputTypeBtnInactive = { ...themed.outputTypeBtnInactive, backgroundColor: ghost, color: panelText, border: panelBorder };

  themed.previewToolbarButtonActive = { ...themed.previewToolbarButtonActive, backgroundColor: 'var(--accent-weak)', border: `2px solid ${accent}`, color: accent };
  themed.previewToolbarButtonInactive = { ...themed.previewToolbarButtonInactive, backgroundColor: ghost, border: panelBorder, color: panelText };

  themed.columnMoveBtnActive = { ...themed.columnMoveBtnActive, backgroundColor: 'var(--accent-weak)', color: accent, border: `1px solid ${accent}` };
  themed.columnMoveBtnInactive = { ...themed.columnMoveBtnInactive, backgroundColor: ghost, color: muted, border: panelBorder };

  themed.screenRemoveBtn = { ...themed.screenRemoveBtn, backgroundColor: 'var(--p-strawberry-500)', color: '#fff', border: '1px solid var(--p-strawberry-500)' };
  themed.screenResetBtn = { ...themed.screenResetBtn, backgroundColor: ghost, color: panelText, border: panelBorder };

  themed.generateButton = { ...themed.generateButton, backgroundColor: accent, color: '#fff', border: `1px solid ${accent}` };
  themed.arenaExportButton = themed.arenaExportButton || styles.arenaExportButton;
  themed.arenaExportButtonHover = themed.arenaExportButtonHover || styles.arenaExportButtonHover;

  themed.applyAllBtn = { ...themed.applyAllBtn, backgroundColor: ghost, color: panelText, border: panelBorder };

  // Row states
  themed.shapeRow = { ...themed.shapeRow, backgroundColor: ghost };
  themed.shapeRowSelected = { ...themed.shapeRowSelected, backgroundColor: 'rgba(255, 149, 0, 0.12)', borderLeft: '2px solid var(--p-orange-500)' };
  themed.shapeRowDisabled = { ...themed.shapeRowDisabled, backgroundColor: 'rgba(0,0,0,0.05)' };

  // Table
  themed.shapesTable = { ...themed.shapesTable, border: panelBorder };
  themed.shapesTableHeader = { ...themed.shapesTableHeader, backgroundColor: 'var(--surface-elevated)', color: muted };
  themed.shapeName = { ...themed.shapeName, color: panelText };
  themed.shapeSummary = { ...themed.shapeSummary, color: muted };
  themed.emptyShapesText = { ...themed.emptyShapesText, color: muted };
  themed.emptyShapesHint = { ...themed.emptyShapesHint, color: muted };

  // Preview / legend
  themed.previewContainer = { ...themed.previewContainer, border: panelBorder, backgroundColor: '#000' };
  themed.previewLegend = { ...themed.previewLegend, backgroundColor: 'rgba(0,0,0,0.72)', border: panelBorder };
  themed.previewSize = { ...themed.previewSize, backgroundColor: 'rgba(0,0,0,0.72)', color: muted };
  themed.previewToolbar = { ...themed.previewToolbar, color: panelText };
  themed.previewToolbarDivider = { ...themed.previewToolbarDivider, backgroundColor: 'var(--panel-border)' };
  themed.sectionIconWrapper = { ...themed.sectionIconWrapper, backgroundColor: 'var(--accent-weak)', border: `1px solid ${accent}`, color: accent };
  themed.sectionIcon = { ...themed.sectionIcon, fill: 'currentColor' };

  // Modal
  themed.floatingNameOverlay = { ...themed.floatingNameOverlay, backgroundColor: 'rgba(0,0,0,0.45)' };
  themed.floatingNameEditor = { ...themed.floatingNameEditor, backgroundColor: panelBg, border: panelBorder, boxShadow: '0 18px 45px rgba(0,0,0,0.35)' };
  themed.modalIconWrapper = { ...themed.modalIconWrapper, backgroundColor: 'var(--accent-weak)', border: `1px solid ${accent}`, color: accent };
  themed.modalIcon = { ...themed.modalIcon, fill: 'currentColor' };
  themed.floatingNameTitle = { ...themed.floatingNameTitle, color: accent };
  themed.floatingNameClose = { ...themed.floatingNameClose, color: muted };
  themed.checkboxLabel = { ...themed.checkboxLabel, color: panelText };
  themed.checkboxHint = { ...themed.checkboxHint, color: muted };

  // Footer
  themed.footer = { ...themed.footer, color: muted, borderTop: panelBorder };

  return themed;
}

// Render the app
const container = document.getElementById('root');
const root = ReactDOM.createRoot(container);
root.render(<Svg2XmlApp />);

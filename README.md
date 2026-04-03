# Advanced Output Toolkit (AOT)

AOT converts vector artwork (SVG and DXF) into Resolume Arena Advanced Output XML. Everything runs in the browser—no installs or build steps. Drop in artwork, review shapes, assign screens, and export ready-to-use XML.

## Why use AOT
- Dual import: SVG or DXF (DXF is converted to SVG on the fly via the `dxf` library).
- Geometry aware: handles paths, polygons, arcs, splines, clip paths, transforms, bezier rasterization, and artboard sizing.
- Projection-friendly: map shapes to screens, toggle slice/mask/both, merge masks, and preview layouts live.
- Zero setup: open `index.html` or use the hosted build; everything loads from CDN.
- Project files: save/load `.rslm` projects to preserve canvas, screens, and per-shape settings.

## Quick start
1) Open `index.html` in a modern browser (or visit the hosted build at https://saccade-studio.github.io/SVG2XML/).
2) Click **Load SVG/DXF File** (or drop a file) and pick your artwork.
3) Adjust canvas size or pick a preset; enable **Use Artboard** if you want to follow the source viewBox/size.
4) Review shapes in the table, set output type (slice/mask/both), rename, and assign screens.
5) Preview the layout; pan/zoom with mouse or trackpad.
6) Export with **Export Resolume XML** and load the XML in Resolume’s Advanced Output.

## Tips
- DXF imports: AOT converts DXF → SVG internally, then processes shapes the same as native SVG.
- Curve detail: increase the bezier resolution if curves look faceted; lower it for lighter output.
- Shape cleanup: options exist to close open paths, skip stroke-only shapes, and extract clip paths.
- Naming: project name can come from file name, SVG title, or a custom value; slices can use type or SVG title.
- Screens: define multiple screens with independent resolutions; `Match Canvas` quickly syncs a screen to the canvas.

## Keyboard & mouse
- Preview: scroll to zoom, click-drag to pan, click shapes to select; point numbers and handles appear when editing polygons.
- Layout UI: sections are draggable/collapsible; split-view option for side-by-side panels and preview.

## Saving & loading
- Projects: use **Save Project** / **Open** to work with `.rslm` files (stores SVG text, layout, and settings).
- Layouts: save/restore UI layout (section order, columns, preview spanning).

## Offline use
- Everything is client-side. If you need to work offline, download the page once and optionally vendor the CDN assets (React, Puppertino, `dxf`) locally; then open `index.html` over `file://` or a simple local server (`python3 -m http.server 8080`).

## Limitations
- Text objects are not exported as text; convert to outlines before import.
- Extremely large or highly detailed artwork can be slower to render in-browser.

## Development
- No build pipeline: edit `app.jsx` and refresh.
- Run a local server for CORS-friendly file access: `python3 -m http.server 8080` and visit http://localhost:8080.

## License
MIT

/* ==========================================================================
   html2stl — app logic
   exocad DentalCAD webview HTML -> extract OpenCTM meshes -> view + export.
   Everything runs client-side. No file ever leaves the browser.
   ========================================================================== */

(function () {
  "use strict";

  var $ = function (id) { return document.getElementById(id); };

  // ----- state -----
  var meshes = [];          // [{ name, type, color, vertices:Float32Array, indices:Uint32Array, tris, verts, dims:[x,y,z], area, threeMesh, material }]
  var baseName = "model";
  var shadeMode = "solid";  // "solid" | "wire"
  var bgDark = true;

  // three.js
  var renderer, scene, camera, controls, meshGroup, gridHelper;

  var PALETTE = ["#ff8a1e", "#4cc9ff", "#3ddc97", "#f5c84c", "#ff6b9d", "#a78bfa", "#22d3ee", "#f97316", "#34d399", "#818cf8"];

  // ----- helpers -----
  function esc(s) { return String(s).replace(/[&<>"']/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]; }); }
  function fmt(n) { return n.toLocaleString("tr-TR"); }
  function humanSize(b) { return b < 1024 ? b + " B" : b < 1048576 ? (b / 1024).toFixed(1) + " KB" : (b / 1048576).toFixed(2) + " MB"; }
  function sanitizeBase(n) { return (n || "model").replace(/\.(html?|htm)$/i, "").replace(/[^\w\-]+/g, "-").replace(/^-+|-+$/g, "") || "model"; }
  function toast(msg) {
    var t = $("toast");
    t.innerHTML = '<span class="toast__dot"></span>' + esc(msg);
    t.classList.add("is-show");
    clearTimeout(toast._t);
    toast._t = setTimeout(function () { t.classList.remove("is-show"); }, 2600);
  }
  function downloadBlob(blob, name) {
    var url = URL.createObjectURL(blob);
    var a = document.createElement("a");
    a.href = url; a.download = name;
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(function () { URL.revokeObjectURL(url); }, 2000);
  }

  function base64ToBytes(b64) {
    b64 = b64.replace(/\s+/g, "");
    var lut = new Int16Array(256).fill(-1);
    var chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    for (var k = 0; k < 64; k++) lut[chars.charCodeAt(k)] = k;
    var len = b64.length, out = new Uint8Array(Math.floor(len * 3 / 4)), p = 0, buf = 0, bits = 0;
    for (var j = 0; j < len; j++) {
      var c = b64.charCodeAt(j);
      if (c === 0x3d) break;
      var v = lut[c];
      if (v < 0) continue;
      buf = (buf << 6) | v; bits += 6;
      if (bits >= 8) { bits -= 8; out[p++] = (buf >> bits) & 0xff; }
    }
    return out.subarray(0, p);
  }

  function indexOfBytes(hay, needle, from) {
    outer: for (var i = from; i <= hay.length - needle.length; i++) {
      for (var j = 0; j < needle.length; j++) if (hay[i + j] !== needle[j]) continue outer;
      return i;
    }
    return -1;
  }

  function rgbHex(r, g, b) {
    return "#" + ("0" + (r & 0xff).toString(16)).slice(-2) + ("0" + (g & 0xff).toString(16)).slice(-2) + ("0" + (b & 0xff).toString(16)).slice(-2);
  }

  // ----- exocad color-definition list -> mesh type names -----
  function extractColorList(html) {
    var marker = "createColorDefinitionList=function(){return[";
    var s = html.indexOf(marker);
    if (s === -1) return [];
    var a = s + marker.length, e = html.indexOf("]}", a);
    var text = html.slice(a, e + 1);
    var re = /Type:"([^"]+)",Color:"(#[0-9A-Fa-f]{6})"/g, list = [], m;
    while ((m = re.exec(text)) !== null) list.push({ type: m[1], color: m[2].toLowerCase() });
    return list;
  }
  function buildColorMap(list) {
    var map = {};
    list.forEach(function (x) { if (!map[x.color]) map[x.color] = x.type; });
    return map;
  }
  var DISPLAY = {
    "OrthoModel": "Model", "ModelPlatelessBase": "Model", "ModelPlateTypeMixed": "Model",
    "ModelPlateTypeHealthy": "Model", "ModelPlatelessDie": "Die", "ModelPlateTypeStump": "Stump",
    "Antagonist": "Antagonist", "UnsegmentedJaw": "Jaw", "UnsegmentedTooth": "Tooth",
    "MergedTooth": "Merged Tooth", "MergedBridge": "Merged Bridge", "MergedPontic": "Merged Pontic",
    "MergedBar": "Merged Bar", "AnatomicCrown": "Crown", "AnatomicPontic": "Pontic"
  };
  function displayName(type) {
    if (DISPLAY[type]) return DISPLAY[type];
    return type.replace(/([A-Z])/g, " $1").replace(/^ /, "").replace(/ +/g, " ");
  }
  function meshType(bytes, octmOffset, colorMap) {
    var lo = octmOffset - 100;
    if (lo >= 0 && lo + 2 < bytes.length) {
      var h = rgbHex(bytes[lo], bytes[lo + 1], bytes[lo + 2]);
      if (colorMap[h]) return colorMap[h];
    }
    for (var i = octmOffset - 256; i < octmOffset - 2; i++) {
      if (i < 0) continue;
      var h2 = rgbHex(bytes[i], bytes[i + 1], bytes[i + 2]);
      if (colorMap[h2]) return colorMap[h2];
    }
    return null;
  }

  // ----- extraction + decode -----
  function computeMeshStats(m) {
    var v = m.vertices, idx = m.indices;
    var minx = Infinity, miny = Infinity, minz = Infinity, maxx = -Infinity, maxy = -Infinity, maxz = -Infinity;
    for (var i = 0; i < v.length; i += 3) {
      var x = v[i], y = v[i + 1], z = v[i + 2];
      if (x < minx) minx = x; if (y < miny) miny = y; if (z < minz) minz = z;
      if (x > maxx) maxx = x; if (y > maxy) maxy = y; if (z > maxz) maxz = z;
    }
    m.dims = [maxx - minx, maxy - miny, maxz - minz];
    var area = 0;
    for (var t = 0; t < idx.length; t += 3) {
      var a = idx[t] * 3, b = idx[t + 1] * 3, c = idx[t + 2] * 3;
      var ux = v[b] - v[a], uy = v[b + 1] - v[a + 1], uz = v[b + 2] - v[a + 2];
      var vx = v[c] - v[a], vy = v[c + 1] - v[a + 1], vz = v[c + 2] - v[a + 2];
      var nx = uy * vz - uz * vy, ny = uz * vx - ux * vz, nz = ux * vy - uy * vx;
      area += 0.5 * Math.sqrt(nx * nx + ny * ny + nz * nz);
    }
    m.area = area;
  }

  function extractMeshes(bytes, colorMap) {
    var magic = [0x4f, 0x43, 0x54, 0x4d];
    var offs = [], from = 0, pos;
    while ((pos = indexOfBytes(bytes, magic, from)) !== -1) { offs.push(pos); from = pos + 4; }
    var result = [];
    for (var i = 0; i < offs.length; i++) {
      var start = offs[i], end = i + 1 < offs.length ? offs[i + 1] : bytes.length;
      try {
        var stream = new CTM.Stream(bytes.subarray(start, end));
        var file = new CTM.File(stream);
        var vertices = file.body.vertices, indices = file.body.indices;
        if (!vertices || !indices || indices.length === 0) continue;
        var type = meshType(bytes, start, colorMap);
        result.push({ name: "", type: type || ("mesh_" + (i + 1)), color: "#fff", vertices: vertices, indices: indices, verts: vertices.length / 3, tris: indices.length / 3 });
      } catch (e) { /* skip */ }
    }
    result.sort(function (a, b) { return b.tris - a.tris; });
    var seen = {};
    result.forEach(function (m, i) {
      var label = displayName(m.type);
      seen[label] = (seen[label] || 0) + 1;
      m.name = seen[label] > 1 ? label + "-" + seen[label] : label;
      m.color = PALETTE[i % PALETTE.length];
      computeMeshStats(m);
    });
    return result;
  }

  // ----- exporters -----
  function stlBinary(mesh) {
    var triCount = mesh.indices.length / 3;
    var buffer = new ArrayBuffer(84 + triCount * 50);
    var dv = new DataView(buffer);
    var hdr = "html2stl — " + mesh.name;
    for (var h = 0; h < 80; h++) dv.setUint8(h, h < hdr.length ? hdr.charCodeAt(h) : 0x20);
    dv.setUint32(80, triCount, true);
    var off = 84, v = mesh.vertices, idx = mesh.indices;
    for (var i = 0; i < idx.length; i += 3) {
      var a = idx[i] * 3, b = idx[i + 1] * 3, c = idx[i + 2] * 3;
      var ax = v[a], ay = v[a + 1], az = v[a + 2], bx = v[b], by = v[b + 1], bz = v[b + 2], cx = v[c], cy = v[c + 1], cz = v[c + 2];
      var ux = bx - ax, uy = by - ay, uz = bz - az, vx = cx - ax, vy = cy - ay, vz = cz - az;
      var nx = uy * vz - uz * vy, ny = uz * vx - ux * vz, nz = ux * vy - uy * vx;
      var l = Math.sqrt(nx * nx + ny * ny + nz * nz) || 1; nx /= l; ny /= l; nz /= l;
      dv.setFloat32(off, nx, true); off += 4; dv.setFloat32(off, ny, true); off += 4; dv.setFloat32(off, nz, true); off += 4;
      dv.setFloat32(off, ax, true); off += 4; dv.setFloat32(off, ay, true); off += 4; dv.setFloat32(off, az, true); off += 4;
      dv.setFloat32(off, bx, true); off += 4; dv.setFloat32(off, by, true); off += 4; dv.setFloat32(off, bz, true); off += 4;
      dv.setFloat32(off, cx, true); off += 4; dv.setFloat32(off, cy, true); off += 4; dv.setFloat32(off, cz, true); off += 4;
      dv.setUint16(off, 0, true); off += 2;
    }
    return new Blob([buffer], { type: "model/stl" });
  }

  function stlAscii(mesh) {
    var v = mesh.vertices, idx = mesh.indices, out = ["solid " + mesh.name];
    for (var i = 0; i < idx.length; i += 3) {
      var a = idx[i] * 3, b = idx[i + 1] * 3, c = idx[i + 2] * 3;
      var ax = v[a], ay = v[a + 1], az = v[a + 2], bx = v[b], by = v[b + 1], bz = v[b + 2], cx = v[c], cy = v[c + 1], cz = v[c + 2];
      var ux = bx - ax, uy = by - ay, uz = bz - az, vx = cx - ax, vy = cy - ay, vz = cz - az;
      var nx = uy * vz - uz * vy, ny = uz * vx - ux * vz, nz = ux * vy - uy * vx;
      var l = Math.sqrt(nx * nx + ny * ny + nz * nz) || 1; nx /= l; ny /= l; nz /= l;
      out.push("  facet normal " + nx.toFixed(6) + " " + ny.toFixed(6) + " " + nz.toFixed(6));
      out.push("    outer loop");
      out.push("      vertex " + ax.toFixed(6) + " " + ay.toFixed(6) + " " + az.toFixed(6));
      out.push("      vertex " + bx.toFixed(6) + " " + by.toFixed(6) + " " + bz.toFixed(6));
      out.push("      vertex " + cx.toFixed(6) + " " + cy.toFixed(6) + " " + cz.toFixed(6));
      out.push("    endloop");
      out.push("  endfacet");
    }
    out.push("endsolid " + mesh.name);
    return new Blob([out.join("\n") + "\n"], { type: "text/plain" });
  }

  function obj(mesh) {
    var v = mesh.vertices, idx = mesh.indices, out = ["# html2stl — " + mesh.name];
    for (var i = 0; i < v.length; i += 3) out.push("v " + v[i] + " " + v[i + 1] + " " + v[i + 2]);
    out.push("o " + mesh.name);
    for (var j = 0; j < idx.length; j += 3) out.push("f " + (idx[j] + 1) + " " + (idx[j + 1] + 1) + " " + (idx[j + 2] + 1));
    return new Blob([out.join("\n") + "\n"], { type: "text/plain" });
  }

  function ply(mesh) {
    var v = mesh.vertices, idx = mesh.indices, nv = v.length / 3, nf = idx.length / 3, out = [];
    out.push("ply", "format ascii 1.0", "comment html2stl");
    out.push("element vertex " + nv);
    out.push("property float x", "property float y", "property float z");
    out.push("element face " + nf);
    out.push("property list uchar int vertex_indices", "end_header");
    for (var i = 0; i < v.length; i += 3) out.push(v[i] + " " + v[i + 1] + " " + v[i + 2]);
    for (var j = 0; j < idx.length; j += 3) out.push("3 " + idx[j] + " " + idx[j + 1] + " " + idx[j + 2]);
    return new Blob([out.join("\n") + "\n"], { type: "text/plain" });
  }

  function exportMesh(mesh, fmtId) {
    var ext = { "stl": "stl", "stl-ascii": "stl", "obj": "obj", "ply": "ply" }[fmtId];
    var blob = fmtId === "stl" ? stlBinary(mesh) : fmtId === "stl-ascii" ? stlAscii(mesh) : fmtId === "obj" ? obj(mesh) : ply(mesh);
    return { blob: blob, name: baseName + "-" + mesh.name + "." + ext };
  }

  // ----- 3D viewer -----
  function initViewer() {
    if (renderer) return;
    renderer = new THREE.WebGLRenderer({ canvas: $("viewerCanvas"), antialias: true });
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    renderer.outputEncoding = THREE.sRGBEncoding;

    scene = new THREE.Scene();
    scene.background = new THREE.Color(0x0e1114);

    camera = new THREE.PerspectiveCamera(45, 1, 0.1, 4000);
    camera.position.set(60, 45, 80);

    controls = new THREE.OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true;
    controls.dampingFactor = 0.09;

    scene.add(new THREE.HemisphereLight(0xffffff, 0x2a3038, 0.85));
    var d1 = new THREE.DirectionalLight(0xffffff, 0.9); d1.position.set(90, 140, 70); scene.add(d1);
    var d2 = new THREE.DirectionalLight(0xffffff, 0.35); d2.position.set(-70, -50, -90); scene.add(d2);

    meshGroup = new THREE.Group();
    scene.add(meshGroup);

    gridHelper = new THREE.GridHelper(200, 40, 0x333a44, 0x1c222a);
    gridHelper.position.y = -60;
    scene.add(gridHelper);

    function resize() {
      var el = $("viewport");
      var w = el.clientWidth, h = el.clientHeight;
      renderer.setSize(w, h, false);
      camera.aspect = w / h;
      camera.updateProjectionMatrix();
    }
    window.addEventListener("resize", resize);
    new ResizeObserver(resize).observe($("viewport"));
    resize();

    (function loop() {
      requestAnimationFrame(loop);
      controls.update();
      renderer.render(scene, camera);
    })();
  }

  function addMeshToScene(m) {
    initViewer();
    var geo = new THREE.BufferGeometry();
    geo.setAttribute("position", new THREE.BufferAttribute(m.vertices, 3));
    geo.setIndex(new THREE.BufferAttribute(m.indices, 1));
    geo.computeVertexNormals();
    var mat = new THREE.MeshStandardMaterial({ color: new THREE.Color(m.color), roughness: 0.55, metalness: 0.04, flatShading: true, side: THREE.DoubleSide, wireframe: shadeMode === "wire" });
    var mesh = new THREE.Mesh(geo, mat);
    mesh.userData.index = meshes.indexOf(m);
    meshGroup.add(mesh);
    m.threeMesh = mesh;
    m.material = mat;
  }

  function fitCamera() {
    if (!meshGroup || meshGroup.children.length === 0) return;
    var box = new THREE.Box3().setFromObject(meshGroup);
    var size = box.getSize(new THREE.Vector3());
    var center = box.getCenter(new THREE.Vector3());
    var maxDim = Math.max(size.x, size.y, size.z) || 1;
    var dist = maxDim / (2 * Math.tan(camera.fov * Math.PI / 360)) * 1.5;
    camera.position.copy(center).add(new THREE.Vector3(dist * 0.55, dist * 0.4, dist));
    camera.near = maxDim / 200; camera.far = maxDim * 200; camera.updateProjectionMatrix();
    controls.target.copy(center); controls.update();
  }

  function orient(dir) {
    if (!meshGroup || meshGroup.children.length === 0) return;
    var box = new THREE.Box3().setFromObject(meshGroup);
    var center = box.getCenter(new THREE.Vector3());
    var size = box.getSize(new THREE.Vector3());
    var d = Math.max(size.x, size.y, size.z) * 1.6;
    if (dir === "front") camera.position.set(center.x, center.y, center.z + d);
    else if (dir === "top") camera.position.set(center.x, center.y + d, center.z + 0.001);
    else if (dir === "right") camera.position.set(center.x + d, center.y, center.z);
    else camera.position.set(center.x + d, center.y + d * 0.7, center.z + d);
    controls.target.copy(center); controls.update();
  }

  function setShade(mode) {
    shadeMode = mode;
    meshes.forEach(function (m) { if (m.material) m.material.wireframe = mode === "wire"; });
  }
  function setGrid(on) {
    if (gridHelper) gridHelper.visible = on;
  }
  function setBg(dark) {
    bgDark = dark;
    if (scene) scene.background = new THREE.Color(dark ? 0x0e1114 : 0xe6e8eb);
  }

  function updateReadout() {
    if (!meshGroup || meshGroup.children.length === 0) return;
    var box = new THREE.Box3().setFromObject(meshGroup);
    var s = box.getSize(new THREE.Vector3());
    $("dimX").textContent = s.x.toFixed(1) + " mm";
    $("dimY").textContent = s.y.toFixed(1) + " mm";
    $("dimZ").textContent = s.z.toFixed(1) + " mm";
  }

  function screenshot() {
    if (!renderer) return;
    renderer.render(scene, camera);
    var a = document.createElement("a");
    a.href = renderer.domElement.toDataURL("image/png");
    a.download = baseName + "-preview.png";
    a.click();
  }

  // ----- mesh panel -----
  function renderPanel() {
    var wrap = $("meshList");
    wrap.innerHTML = meshes.map(function (m, i) {
      return (
        '<div class="mesh" data-i="' + i + '">' +
          '<div class="mesh__check">✓</div>' +
          '<div class="mesh__dot" style="background:' + m.color + '"></div>' +
          '<div class="mesh__main">' +
            '<div class="mesh__name">' + esc(m.name) + '</div>' +
            '<div class="mesh__stats">' + fmt(m.tris) + ' üçgen · ' + fmt(m.verts) + ' nokta · ' + m.area.toFixed(0) + ' mm²</div>' +
            '<div class="mesh__dim">' + m.dims.map(function (d) { return d.toFixed(1); }).join(" × ") + ' mm</div>' +
          '</div>' +
          '<div class="mesh__actions">' +
            '<button class="mesh__btn mesh__eye" data-i="' + i + '" title="Görünürlük">👁</button>' +
            '<button class="mesh__btn mesh__dl" data-i="' + i + '" title="İndir">⬇</button>' +
          '</div>' +
        '</div>'
      );
    }).join("");
  }

  function updateTopbar() {
    $("fileNameTag").textContent = baseName + ".html";
    $("statMeshes").textContent = meshes.length;
    var tris = 0, verts = 0;
    meshes.forEach(function (m) { tris += m.tris; verts += m.verts; });
    $("statTris").textContent = fmt(tris);
    $("statSize").textContent = fmt(verts) + " nokta";
  }

  function selectedIndices() {
    return Array.from(document.querySelectorAll(".mesh.is-selected")).map(function (el) { return +el.dataset.i; });
  }

  // ----- actions -----
  function handleFile(file) {
    if (!file) return;
    if (!/\.html?$/i.test(file.name)) { toast("Lütfen .html veya .htm dosyası seç"); return; }
    baseName = sanitizeBase(file.name);

    var reader = new FileReader();
    reader.onload = function () {
      try {
        var html = reader.result;
        var re = /DentalWebGL\.m_Data\s*=\s*\{["']data["']:\s*["']([A-Za-z0-9+/=]+)["']\s*\}/g;
        var m, b64 = null;
        while ((m = re.exec(html)) !== null) b64 = m[1];
        if (!b64) throw new Error("m_Data bulunamadı (bu bir exocad webview dosyası mı?)");

        var colorMap = buildColorMap(extractColorList(html));
        var bytes = base64ToBytes(b64);
        meshes = extractMeshes(bytes, colorMap);
        if (!meshes.length) throw new Error("Mesh bulunamadı");

        // clear old scene
        if (meshGroup) {
          meshGroup.traverse(function (o) { if (o.isMesh) { o.geometry && o.geometry.dispose(); o.material && o.material.dispose(); } });
          while (meshGroup.children.length) meshGroup.remove(meshGroup.children[0]);
        }
        meshes.forEach(addMeshToScene);
        fitCamera();
        updateReadout();

        $("vLoading").hidden = true;
        $("landing").hidden = true;
        $("workspace").hidden = false;
        $("topbarCenter").hidden = false;
        $("btnExportAll").hidden = false;
        renderPanel();
        updateTopbar();
        toast(meshes.length + " mesh çıkarıldı");
      } catch (e) {
        toast("Hata: " + e.message);
      }
    };
    reader.readAsText(file);
  }

  function downloadZip(indices) {
    if (!window.JSZip) { toast("JSZip yüklenemedi"); return; }
    var fmt = $("fmtSelect").value;
    var zip = new JSZip();
    indices.forEach(function (i) {
      var ex = exportMesh(meshes[i], fmt);
      zip.file(ex.name, ex.blob);
    });
    zip.generateAsync({ type: "blob" }).then(function (blob) {
      downloadBlob(blob, baseName + "-meshes.zip");
      toast(indices.length + " mesh indirildi");
    });
  }

  // ----- events -----
  var fileInput = $("fileInput");
  function pick() { fileInput.click(); }
  $("btnUpload").addEventListener("click", pick);
  $("btnUploadTop").addEventListener("click", pick);
  fileInput.addEventListener("change", function () { handleFile(fileInput.files[0]); });

  // global drag & drop
  window.addEventListener("dragover", function (e) { e.preventDefault(); });
  window.addEventListener("drop", function (e) {
    e.preventDefault();
    var f = e.dataTransfer.files && e.dataTransfer.files[0];
    if (f && /\.html?$/i.test(f.name)) handleFile(f);
  });

  // view controls
  $("shadeSolid").addEventListener("click", function () { setShade("solid"); this.classList.add("is-active"); $("shadeWire").classList.remove("is-active"); });
  $("shadeWire").addEventListener("click", function () { setShade("wire"); this.classList.add("is-active"); $("shadeSolid").classList.remove("is-active"); });
  $("gridOn").addEventListener("click", function () { setGrid(!(gridHelper && gridHelper.visible)); this.classList.toggle("is-active", gridHelper && gridHelper.visible); });
  $("bgToggle").addEventListener("click", function () { setBg(!bgDark); });
  Array.prototype.forEach.call(document.querySelectorAll("[data-orient]"), function (b) {
    b.addEventListener("click", function () { orient(this.getAttribute("data-orient")); });
  });
  $("btnFit").addEventListener("click", fitCamera);
  $("btnScreenshot").addEventListener("click", screenshot);

  // panel
  $("btnSelectAll").addEventListener("click", function () {
    var rows = document.querySelectorAll(".mesh");
    var all = rows.length && Array.from(rows).every(function (r) { return r.classList.contains("is-selected"); });
    rows.forEach(function (r) { r.classList.toggle("is-selected", !all); });
  });
  $("meshList").addEventListener("click", function (e) {
    var row = e.target.closest(".mesh");
    if (!row) return;
    var i = +row.dataset.i, m = meshes[i];
    if (e.target.closest(".mesh__dl")) { e.stopPropagation(); var ex = exportMesh(m, $("fmtSelect").value); downloadBlob(ex.blob, ex.name); toast(m.name + " indirildi"); return; }
    if (e.target.closest(".mesh__eye")) { e.stopPropagation(); m.threeMesh.visible = !m.threeMesh.visible; row.classList.toggle("is-hidden", !m.threeMesh.visible); updateReadout(); return; }
    row.classList.toggle("is-selected");
  });
  $("fmtSelect").addEventListener("change", function () { renderPanel(); });
  $("btnDownloadSelected").addEventListener("click", function () {
    var sel = selectedIndices();
    if (!sel.length) return toast("Önce mesh seçin");
    downloadZip(sel);
  });
  $("btnDownloadAll").addEventListener("click", function () {
    if (!meshes.length) return;
    downloadZip(meshes.map(function (_, i) { return i; }));
  });
  $("btnExportAll").addEventListener("click", function () {
    if (!meshes.length) return;
    downloadZip(meshes.map(function (_, i) { return i; }));
  });
})();

/*
  B2R2 - the Next-Generation Reversing Platform

  Author: Subin Jeong <cyclon2@kaist.ac.kr>
          Soomin Kim <soomink@kaist.ac.kr>
          Sang Kil Cha <sangkilc@kaist.ac.kr>

  Copyright (c) SoftSec Lab. @ KAIST, since 2016

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
*/

class SideBarItem {
  constructor(d) {
    this.icon = d.icon;
    this.id = d.id;
    this.contentid = d.contentid;
    this.name = d.name;
    this.active = d.active;
  }

  open() {
    $(this.contentid).show();
    this.active = true;
    $(this.id).addClass("active");
  }

  addWindow(dims, newDocument, num) {
    const minimapid = "#minimap-" + num;
    const cfgid = "#cfg-" + num;

    if ($(newDocument).find(minimapid).length == 0) {
      const miniMapTemplate = String.format(b2r2.R.miniMapTemplate, num);
      $(newDocument).find("#id_new-minimap-div").append(miniMapTemplate);
    }
    if ($(newDocument).find(cfgid).length == 0) {
      const graphDivTemplate = String.format(b2r2.R.graphDivTemplate, num);
      $(newDocument).find("#id_new-graph-container").append(graphDivTemplate);
    }

    // minimize the new minimap when it is minimized.
    if ($(newDocument).find("#id_new-minimap-div").hasClass("active")) {
      d3.select(newDocument).select(minimapid)
        .style("border", "unset")
        .style("height", "0")
    }

    d3.select(newDocument).select(cfgid)
      .attr("width", dims.cfgVPDim.width)
      .attr("height", dims.cfgVPDim.height)
  }

  openWindow() {
    const self = this;
    let newWindow = window.open("", '_blank', 'height=800,width=1200,toolbar=no');
    newWindow.addEventListener('load', function () {

    });
    newWindow.document.write(String.format(b2r2.R.newWindowHeadTemplate, "Call Graph"));
    newWindow.document.write(String.format(b2r2.R.newWindowTemplate, "new", 11));
    let funcName;
    if (funcName == undefined || funcName == "") {
      funcName = $("#funcSelector li:first").text();
    }
    query({
      "q": "cfg-CG",
      "args": funcName
    },
      function (status, json) {
        if (Object.keys(json).length > 0) {
          let dims = reloadUI({
            document: newWindow.document,
            graphContainerId: "#id_new-graph-container",
            mainContainerId: "#id_new-main-container",
            tabContainerId: ""
          });
          let tabtemp = 11;
          self.addWindow(dims, newWindow.document, tabtemp);
          let contextmenu = new ContextMenu({
            document: newWindow.document,
            id: "id_new-contextmenu"
          });
          contextmenu.registerEvents();
          let g = new FlowGraph({
            document: newWindow.document,
            graphContainer: "#id_new-graph-container",
            minimapContainer: "#id_new-minimap-div",
            tab: tabtemp,
            newWindow: true,
            cfg: "#cfg-" + tabtemp,
            stage: "#cfgStage-" + tabtemp,
            group: "#cfgGrp-" + tabtemp,
            minimap: "#minimap-" + tabtemp,
            minimapStage: "#minimapStage-" + tabtemp,
            minimapViewPort: "#minimapVP-" + tabtemp,
            contextmenu: contextmenu,
            dims: dims,
            json: json
          });
          g.drawGraph();
          let autoComplete = new AutoComplete({
            document: newWindow.document,
            id: "#id_new-autocomplete-list",
            inputid: "#id_new-address-search"
          });
          autoComplete.registerEvents();
          autoComplete.reload(g);
        }
      });
  }

  close() {
    $(this.contentid).hide();
    this.active = false;
    $(this.id).removeClass("active");
  }

  registerEvents() {

  }
}

class SideBar {
  constructor(d) {
    this.items = d.items;
  }

  add(item) {
    this.items.push(item);
  }

  open(id) {
    if (id === "#id_sidebar-callgraph")
      return;
    for (let k in this.items) {
      if (this.items[k].id === id) {
        this.items[k].open();
      } else {
        this.items[k].close();
      }
    }
  }

  get(id) {
    for (let k in this.items) {
      if (this.items[k].id === id) {
        return this.items[k];
      }
    }
  }

  resizeSidebar(callback) {
    const minimum_size = 100;
    const resizer = document.getElementById("id_resize-sidebar");
    const element = document.getElementById("id_sidebar-content");
    let original_mouse_x = 0;
    let original_width = 0;
    resizer.addEventListener('mousedown', function (e) {
      e.preventDefault();
      original_width = parseFloat(getComputedStyle(element, null).getPropertyValue('width').replace('px', ''));
      original_mouse_x = e.pageX;
      window.addEventListener('mousemove', resize);
      window.addEventListener('mouseup', stopResize);
    });
    function resize(e) {
      const width = original_width + (e.pageX - original_mouse_x);
      if (width > minimum_size) {
        element.style.width = width + 'px';
        element.style.minWidth = width + 'px';
        element.style.maxWidth = width + 'px';
        $(".sidebar-content-item").each(function () {
          $(this).css("max-width", width);
          $(this).css("min-width", width);
          $(this).css("width", width);
          callback();
        });
      }
    }
    function stopResize() {
      window.removeEventListener('mousemove', resize);
    }
  }

  registerEvents() {
    const self = this;
    $(document).on("click", ".sidebar-item", function () {
      let id = $(this).attr("id");
      if (id === "id_sidebar-callgraph") {
        self.get("#" + id).openWindow();
      } else {
        self.open("#" + id);
      }
    });
    self.resizeSidebar(reloadUI);
  }
}

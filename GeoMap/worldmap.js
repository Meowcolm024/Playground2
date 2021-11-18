// script for the world map

/** 
 * This source code is modified from
 * https://leafletjs.com/examples/choropleth/ 
*/

var map = L.map('map').setView([53, 13], 4);

L.tileLayer('https://api.mapbox.com/styles/v1/{id}/tiles/{z}/{x}/{y}?access_token=pk.eyJ1IjoibWFwYm94IiwiYSI6ImNpejY4NXVycTA2emYycXBndHRqcmZ3N3gifQ.rJcFIG214AriISLbB6B5aw', {
    maxZoom: 18,
    attribution: 'Map data &copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors, ' +
        'Imagery © <a href="https://www.mapbox.com/">Mapbox</a>',
    id: 'mapbox/light-v9',
    tileSize: 512,
    zoomOffset: -1
}).addTo(map);

// colors are fixed
let cs = ['#b10026', '#e31a1c', '#fc4e2a', '#fd8d3c', '#feb24c', '#ffffcc']

// get color using iso code and related data
function getColor(d) {
    if (!datapack[d])
        return '#FFFFFF'
    for (var i = 0; i < cs.length; i++) {
        if (datapack[d] >= gs[i])
            return cs[i];
    }
}

function style(feature) {
    return {
        fillColor: getColor(feature.properties.iso_a3),
        weight: 2,
        opacity: 1,
        dashArray: '3',
        color: 'white',
        fillOpacity: 0.7
    };
}

function highlightFeature(e) {
    var layer = e.target;

    layer.setStyle({
        weight: 5,
        color: '#666',
        dashArray: '',
        fillOpacity: 0.7
    });

    if (!L.Browser.ie && !L.Browser.opera && !L.Browser.edge) {
        layer.bringToFront();
    }

    let name = layer.feature.properties.name        // region name
    let code = layer.feature.properties.iso_a3      // region iso code
    info.update(name, datapack[code]);
}

var geojson

function resetHighlight(e) {
    geojson.resetStyle(e.target);
    info.update();
}
function zoomToFeature(e) {
    map.fitBounds(e.target.getBounds());
}

function onEachFeature(feature, layer) {
    layer.on({
        mouseover: highlightFeature,
        mouseout: resetHighlight,
        click: zoomToFeature
    });
}

// ---------

var info = L.control();

info.onAdd = function (map) {
    this._div = L.DomUtil.create('div', 'info'); // create a div with a class "info"
    this.update();
    return this._div;
};

// method that we will use to update the control based on feature properties passed
info.update = function (x, y) {
    this._div.innerHTML =
        '<h4>Covid Data</h4>' +
        'on ' + dateTitle + '<br>' +
        (x ? '<b>' + x + '</b><br />' +
            (y ? y + infoTitle : 'No data')
            : 'Hover over a country/region');
};

info.addTo(map);

// --------

var legend = L.control({ position: 'bottomright' });

legend.onAdd = function (map) {

    var div = L.DomUtil.create('div', 'info legend')

    // loop through our density intervals and generate a label with a colored square for each interval
    for (var i = 0; i < cs.length; i++) {
        div.innerHTML +=
            '<i style="background:' + cs[i] + '"></i> ' +
            (i == 0 ? gs[i] + '+' : gs[i] + ' ~ ' + gs[i - 1])
            + '<br>';
    }

    div.innerHTML += '<i style="background: #FFFFFF"></i> No data <br>';

    return div;
};

legend.addTo(map);

geojson = L.geoJson(countriesData, { style: style, onEachFeature: onEachFeature }).addTo(map);

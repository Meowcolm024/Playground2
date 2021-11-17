// script for the world map

var map = L.map('map').setView([53, 13], 4);

L.tileLayer(
    "https://stamen-tiles.a.ssl.fastly.net/toner-lite/{z}/{x}/{y}@2x.png" // stamen toner tiles
).addTo(map);

// colors ar efixed
let cs = ['#b10026', '#e31a1c', '#fc4e2a', '#fd8d3c', '#feb24c', '#ffffcc']

// we can ffi with this to color using covid info
function getColor(d) {
    for (var i = 0; i < cs.length; i++) {
        if (!datapack[d])
            return '#FFFFFF'
        if (datapack[d] < gs[i])
            continue;
        return cs[i];
    }
}

function style(feature) {
    return {
        // get population
        // in the project we will pass data from java using name
        fillColor: getColor(feature.properties.name),
        weight: 2,
        opacity: 1,
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
}

function resetHighlight(e) {
    geojson.resetStyle(e.target);
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

var legend = L.control({ position: 'bottomright' });

legend.onAdd = function (map) {

    var div = L.DomUtil.create('div', 'info legend')

    // loop through our density intervals and generate a label with a colored square for each interval
    for (var i = 0; i < cs.length; i++) {
        div.innerHTML +=
            '<i style="background:' + cs[i] + '"></i> ' + gs[i] + '<br>';
    }

    div.innerHTML += reportTitle

    return div;
};

legend.addTo(map);

L.geoJson(countriesData, { style: style, onEachFeature: onEachFeature }).addTo(map);

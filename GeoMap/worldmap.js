// script for the world map

var map = L.map('map').setView([53, 13], 4);

L.tileLayer(
    "https://stamen-tiles.a.ssl.fastly.net/toner-lite/{z}/{x}/{y}@2x.png" // stamen toner tiles
).addTo(map);

// we can ffi with this to color using covid info
function getColor(d) {
    return d > 500000000 ? '#b10026' :
        d > 100000000 ? '#e31a1c' :
            d > 50000000 ? '#fc4e2a' :
                d > 25000000 ? '#fd8d3c' :
                    d > 10000000 ? '#feb24c' :
                        d > 5000000 ? '#fed976' :
                            d > 2500000 ? '#ffeda0' :
                                d < 2500000 ? '#ffffcc' :
                                    '#FFFFFF';
}

function style(feature) {
    return {
        // get population
        // in the project we will pass data from java using name
        fillColor: getColor(feature.properties.pop_est),
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

    var div = L.DomUtil.create('div', 'info legend'),
        // ingetColor
        grades = [0, 2500000, 5000000, 10000000, 25000000, 50000000, 100000000, 500000000],
        labels = [];

    // loop through our density intervals and generate a label with a colored square for each interval
    for (var i = 0; i < grades.length; i++) {
        div.innerHTML +=
            '<i style="background:' + getColor(grades[i] + 1) + '"></i> ' +
            grades[i] + (grades[i + 1] ? '&ndash;' + grades[i + 1] + '<br>' : '+');
    }

    return div;
};

legend.addTo(map);

L.geoJson(countriesData, { style: style, onEachFeature: onEachFeature }).addTo(map);
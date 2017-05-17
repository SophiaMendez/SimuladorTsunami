/*
Universidad del Valle de Guatemala
Claudia Sophia Méndez Belloso
Carné 12732
2017
index.js
*/

var outputDiv=null;
var map = null;
var mapMarkers=new Array(0);
var gridWidth = 10; //ancho de mallas internas 
var gridHeight = 10;
var halfGridWidth = gridWidth/2;
var bigGridDimension = 5;
var gridSector = 1000; // in meters
var shootLines = 10;
var linePoints = 10;
var originIndex = shootLines * 5;


var blockQueue = [];
var blockWidth = 5;
var blockCenter = 2;

var nextCallTime = 2000;
var elevator = null;
var maxWaveHeight = 500;
var maxRange = 100000;
var mappingInProgress = 0;
var currLocation = null;
var initialClickTaken = 0;
var clickedLocation = null;
var clickedAngle = 0;
var mapMoveListenerHandle = null;
var firstClickTakenListenerHandle = null;
var marker = null;
var markers = [];


// Objeto measure para el calculo de longitud y area
var measure = {
	mvcLine: new google.maps.MVCArray(),
	mvcPolygon: new google.maps.MVCArray(),
	mvcMarkers: new google.maps.MVCArray(),
	line: null,
	polygon: null
};

//de acuerdo a la escala de tsunamis de Imamura
// Escala: 		   -		0			1			2			3			4
var waveSizeArr = [0,		2,			5,			10,			20,			30];
var waveRangeArr = [0,		250,		500,		1000,		1500,		2000]; //rango que abarca en km

//codigo para el mapa principal (gridMap)
var notMapped = 0;
var tooHigh = 1; // tierra que no se inundara
var filledWithWater = 2; //tierra inundada
var unfilled = 3; // tierra que se inundara

// codigo para el estado al completar
var IN_PROGRESS = 0;
var COMPLETE_ALL_WATER = 1;
var COMPLETE_MIXED = 2;

// funcion para desplegar los mensajes en la interfaz
function setOutputMsg(msg){
	outputDiv.innerHTML= msg;
	outputDiv.className = 'outputStyle';
}

// funcion para verificar si un valor es numerico
function IsNumeric(n) {
	var returnValue = (!isNaN(parseFloat(n)) && isFinite(n));
	return returnValue;
}

function between(x, min, max) {
  return x >= min && x < max;
}

// funcion para setear el length promedio de la ola inicial respecto a la profundidad
function setWavelength(depth){
	var wavelength = null;

	if(depth >= 5500){
		wavelength = 282;
	}
	else if (between(depth, 3000, 5500)){
		wavelength = 213;
	}
	else if (between(depth, 1100, 3000)){
		wavelength = 151;
	}
	else if (between(depth, 125, 1100)){
		wavelength = 48;
	}
	else if (between(depth, 30, 125)){
		wavelength = 23;
	}
	else if (between(depth, 0, 30)){
		wavelength = 11;
	}
	return wavelength;
}

// determina en la matriz cuales celdas se van a inundar y cuales no
function mapResultsToMapGrid(mapGrid, locationGrid, currMapPosn, results, waveHeight, locations){
	// given results - map these into mapGr startd 
	var j = 0;
	var i = 0;
	var index = 0;
	
	var blockStartIndex = (parseInt(currMapPosn / blockWidth) * (gridWidth * gridWidth * bigGridDimension)) +
			((4 - (currMapPosn % blockWidth)) * gridWidth);

	for (i = 0; i < gridWidth; i++){
		for (j = 0; j < gridWidth; j++){
			index = blockStartIndex + (j * blockWidth * gridWidth) + i;
			locationGrid[index] = locations[(i * gridWidth) + j];
			
			//results es la matriz de batimetria para todos los puntos
			if (getElev(results, (i * gridWidth) + j) > waveHeight){
				//al calcular si la ola es mas alta que la batimetria en ese punto, determina el estado: tooHigh o unfilled
				mapGrid[index] = tooHigh; // la ola no inundara ese punto
			}
			else{
				mapGrid[index] = unfilled; //ese punto esta sin llenar
			}
		}		
	}
	//measureDistanceX(locationGrid);
}

function measureDistanceX(locationGrid){
	var i = 0;
	var j = 0;
	var coord1 = null;
	var coord2 = null;
	var distance = 0;
	var distX = 0;
	var distProm = 0; //distancia promedio de una fila
	var ejeX = []; //array que contiene las distancias promedio de todas las filas
	var x = 0; //distancia inicial = 0m.

	console.log("length del locationGrid[] " + locationGrid.length);
	for (i = 0; i < (gridWidth * bigGridDimension); i++){
		for (j = 0; j < (gridWidth * bigGridDimension); j++){
			if(i!=0) {
				coord1 = locationGrid[(i*gridWidth*bigGridDimension)];
				coord2 = locationGrid[((i-1)*gridWidth*bigGridDimension)];
				console.log(coord1 + ", " + coord2);
				distance = Math.abs(google.maps.geometry.spherical.computeDistanceBetween(coord1, coord2));
				distX += distance;
			}
		}
		distProm = parseInt(distX/(gridWidth*bigGridDimension));
		x += distProm;
		ejeX.push(x);
		distProm = 0;
	}
}

function gup(name)	{
  name = name.replace(/[\[]/,"\\\[").replace(/[\]]/,"\\\]");
  var regexS = "[\\?&]"+name+"=([^&#]*)";
  var regex = new RegExp( regexS );
  var results = regex.exec( window.location.href );
  if( results == null )
	return null;
  else
	return results[1];
}

// a partir de la posicion actual, verifica si puede propagarse hacia la izquierda
function canSpreadToLeft(mapGrid, currMapPosn){
	var response = 1;

	if ((currMapPosn % blockWidth) > blockCenter)
		response = 0;
	if ((currMapPosn % blockWidth) == 0)
		response = 0;
	
	return response;
}

// a partir de la posicion actual, verifica si puede propagarse hacia la derecha
function canSpreadToRight(mapGrid, currMapPosn){
	var response = 1;

	if ((currMapPosn % blockWidth) < blockCenter)
		response = 0;
	if ((currMapPosn % blockWidth) == (blockWidth-1))
		response = 0;

	return response;
}

// a partir de la posicion actual, verifica si puede propagarse hacia arriba
function canSpreadToUp(mapGrid, currMapPosn){
	var response = 0;

	if (((currMapPosn % blockWidth) == blockCenter) && currMapPosn<((blockWidth-1) * blockWidth))
		response = 1;

	return response;
}

function initialize() 
{
	var lat =  gup('lat');
	var lng =  gup('lng');
	var dir =  gup('dir');
	var hgt =  gup('hgt');
	var rng =  gup('rng');

	if (hgt!=null && hgt!='null' && dir!=null && rng!=null && rng!='null'){
		document.getElementById('WaveHeight').value = hgt;
		document.getElementById('Range').value = rng;
		
		var index = 0;
		var height = Math.round(parseFloat(hgt)*100)/100;
		while (waveSizeArr[index]<height && index<waveSizeArr.length){
			index++;
		}
		if (index>=waveSizeArr.length){
			index = waveSizeArr.length - 1;
		}
		
		document.getElementById('Scale').selectedIndex = index;
	}
	else{
		var reDrawButton = document.getElementById("reDraw");
		reDrawButton.style.display = "none";
	}
	
	// si no se selecciona alguna escala de intensidad de tsunami, seteara una escala = 0, donde la altura de ola son 2 m. y abarcara un rango de 250 km. que es aproximadamente lo que mide el ancho de la costa sur de Guatemala
	if (hgt==null){
		document.getElementById('WaveHeight').value = 2; //m
	}

	if (rng==null){
		document.getElementById('Range').value = 250; //km
	}

	if (typeof console == "undefined") {
		this.console = {log: function() {}};
	}

	if (lat == null){
		
		// inicia centrado en la costa sur de Guatemala
		lat = 13.915706031195674;
		lng = -91.23521842956543; //-90.83521842956543;
	}

	// establece los parametros iniciales del mapa que se cargará
	var latlng = new google.maps.LatLng(lat, lng);
	var myOptions = {
		zoom: 9,
		center: latlng,
		mapTypeId: google.maps.MapTypeId.ROADMAP
	};

	map = new google.maps.Map(document.getElementById("map-canvas"), myOptions);
	outputDiv=document.getElementById('outputDiv');	
	
	map.setOptions({draggableCursor:'crosshair'});
	
	// Crea el ElevationService
	elevator = new google.maps.ElevationService();

	// crea un listener para el click que se haga sobre el mapa y llama a la funcion drawTsunamiMapForEvent en ese punto
	firstClickTakenListenerHandle = google.maps.event.addListener(map, 'click', drawTsunamiMapForEvent);

	// Si se tienen todos los parametros, entonces dibuja la propagacion
	if (lat!=null && lng!=null && dir!=null && hgt!=null){
		mappingInProgress = 1;
		simulateTsunamiPropagation(latlng, dir, hgt, null, -1, dir, null, null, rng);
	}

	// el input de la ubicacion del epicentro
	var searchElem = (	document.getElementById('searchInput'));

	// setea los limites en todo el mapa completo
	var defaultBounds = new google.maps.LatLngBounds(
		new google.maps.LatLng(-90, -180),
		new google.maps.LatLng(90, 180));
	
	var options = {
			bounds: defaultBounds,
			types: [] };
	
	// para hacer el autocomplete al momento de buscar una ubicacion	
	var autocomplete = new google.maps.places.Autocomplete(searchElem, options);	
	google.maps.event.addListener(autocomplete, 'place_changed', function() {
		var place = autocomplete.getPlace();
		
		if (!place.geometry) {
		  return;
		}

		// Si el lugar buscado tiene una geometria, mostrarla en el mapa
		if (place.geometry.viewport) {
		  map.fitBounds(place.geometry.viewport);
		} else {
		  map.setCenter(place.geometry.location);
		  map.setZoom(9);  
		}

		var address = '';
		if (place.address_components) {
		  address = [
			(place.address_components[0] && place.address_components[0].short_name || ''),
			(place.address_components[1] && place.address_components[1].short_name || ''),
			(place.address_components[2] && place.address_components[2].short_name || '')
		  ].join(' ');
		}		
		
	});
	
}

// Basado en el ejemplo de https://developers.google.com/maps/documentation/javascript/examples/geocoding-reverse
function geocodeLatLng() {
	var geocoder = new google.maps.Geocoder;
	var infowindow = new google.maps.InfoWindow;
	var input = document.getElementById('searchInput').value;
	var latlngStr = input.split(',', 2);
	var latlng = {
		lat: parseFloat(latlngStr[0]),
		lng: parseFloat(latlngStr[1])
	};

	// hay casos en que el Geocoder no logra reconocer un punto si está situado sobre el oceano, entonces mostrará un error y sera necesario ingresar manualmente el punto de inicio, marcandolo sobre el mapa
	geocoder.geocode({'location': latlng}, function(results, status) {
		if(status === google.maps.GeocoderStatus.OK) {
			if(results[1]) {
				addMarker(latlng);
			}
			else{
				window.alert('No se encontraron resultados');
			}
		}
		else if(status === google.maps.GeocoderStatus.ZERO_RESULTS){
			window.alert('Esta ubicación no es soportada por Google Maps Geocoder.\nIngrese la ubicación inicial manualmente, señalando el epicentro en el mapa.');
		}
		else{
			window.alert('Geocoder falló debido a: ' + status);
		}
	});
}

// añade un marcador al lugar que se buscaba
function addMarker(location) {
  var marker = new google.maps.Marker({
    position: location,
    map: map
  });
  markers.push(marker);
}

// coloca todos los marcadores en el mapa
function setMapOnAll(map) {
  for (var i = 0; i < markers.length; i++) {
    markers[i].setMap(map);
  }
}

// borra los marcadores del mapa
function clearMarkers() {
  setMapOnAll(null);
}

// elimina todos los marcadores
function deleteMarkers() {
  clearMarkers();
  markers = [];
  document.getElementById("searchInput").value = " ";
}

// Construye la propagacion en una malla, tomando como parametros un angulo de direccion y nuestra posicion de origen(latLong)
function getSpreadLocations(angle, latLong){
	//locations es un array de posiciones (latLong) que indican la posicion y rumbo que tomará cada celda de la malla de propagacion
	var locations = [];

	var outLineNumber = 0;
	
	var tmpAngle = parseFloat(angle) + 90;
	if (tmpAngle>360) tmpAngle = tmpAngle - 360; // si el angulo es mayor a 360, lo resta 360 para dejarlo en la misma posicion. es solo con el fin de que el valor del angulo este dentro del rango permitido para la funcion
	
	// a la funcion computeOffset se le debe pasar como parametros un punto de origen(latLong), una distancia de recorrido, y un angulo de direccion
	var topLeft = google.maps.geometry.spherical.computeOffset(latLong, (gridWidth / 2) * gridSector, 
			tmpAngle);
	
	var startLineDirection = tmpAngle + 180;
	if (startLineDirection>361) startLineDirection = startLineDirection - 360;
	
	while (outLineNumber < shootLines){
		//calcula el nuevo punto en la nueva linea en que se propagara en base al punto anterior, la distancia, y el angulo de direccion en la que va
		var lineStart = google.maps.geometry.spherical.computeOffset(topLeft, outLineNumber * gridSector, 
			startLineDirection);
		// el resultado lo inserta en el array de posiciones final
		locations.push(lineStart);
		
		var traceLineNumber = 1;
		while (traceLineNumber<linePoints){
			// calcula el nuevo punto en que se propagara al punto anterior en la linea que iniciara, la distancia y el angulo de direccion en la que va
			var curLatLng = google.maps.geometry.spherical.computeOffset(lineStart, 
				traceLineNumber * gridSector, angle);
			// el resultado lo inserta en el array final de posiciones
			locations.push(curLatLng);
			traceLineNumber = traceLineNumber + 1;
		}
		
		outLineNumber = outLineNumber + 1;
	}
	return locations;
}

// revisa que todos los sectores en tierra hayan sido clasificados como "tooHigh" o "unfilled"
function getCompletionStatus(mapGrid){
	var result = COMPLETE_ALL_WATER;
	
	for (var x = 0; (x<mapGrid.length && result!=IN_PROGRESS);x++){
		if (mapGrid[x] == notMapped){
			result = IN_PROGRESS;
		}
		else if (mapGrid[x] == tooHigh || mapGrid[x] == unfilled){
			result = COMPLETE_MIXED;
		}
	}
	return result;
}

// devuelve la elevacion en el index dado, extrayendola de la matriz de elevaciones proporcionada por el ElevatorService de Google. lo redondea a 3 cifras decimales
function getElev(elevations, index){
	return (Math.round(parseFloat(elevations[index].elevation.toFixed(3))*100)/100);
}

// revisa todas las celdas, realiza la inundacion cambiando todas las celdas que digan "unfilled" a "filledWithWater"
function performFloodFill(mapGrid, currMapPosn){

	// primero busca el primer sector que esta bajo el agua, en la primera fila
	var foundFirst = 0;
	var results = [];
	var queue = [];
	var x = 0;
	
	if (currMapPosn == blockCenter){
		var originIndex = currMapPosn * gridWidth + (gridWidth/2);
		var blockStart = blockCenter * gridWidth;
		var blockFin = ((blockCenter + 1) * gridWidth) -1;
				
		// recorre el GridMap y setea todos aquellos que estan como "filledWithWater" a "unfilled"
		for (x=0;x<mapGrid.length;x++){
			if (mapGrid[x] == filledWithWater) mapGrid[x] = unfilled;
		}
				
		//inicia desde el punto de origen en el bloque de en medio y se mueve hacia arriba para encontrar el primer inundado
		for (x=originIndex;(x<blockFin && !foundFirst);x+=1){
		
			if (mapGrid[x]==filledWithWater || mapGrid[x]==unfilled){
				queue.push(x);
				foundFirst = 1;
				console.log("encontro un foundFirst");

			}
		}
		
		if (!foundFirst){
			console.log("NO encontro un foundFirst");
			// inicia desde el origen y se mueve hacia abajo para encontrar el primer inundado
			for (x=originIndex;(x>blockStart && !foundFirst);x-=linePoints){
			
				if (mapGrid[x]==filledWithWater || mapGrid[x]==unfilled){
					queue.push(x);
				
					foundFirst = 1;
				}
			}
		}		
	}
	else{
		// se mueve alrededor para encontrar aquellas secciones del borde que estan en el agua
		var index = 0;
		
		var blockStartIndex = (parseInt(currMapPosn / blockWidth) * (gridWidth * gridWidth * bigGridDimension)) +
			((4 - (currMapPosn % blockWidth)) * gridWidth);
		
		// hacia abajo
		if (currMapPosn>bigGridDimension-1){
			for (index = blockStartIndex; index < (blockStartIndex + gridWidth);index++){
			
				if (mapGrid[index - (gridWidth * bigGridDimension)]==filledWithWater){
					queue.push(index);
				}
			}
		}
		
		// hacia la izquierda
		if ((currMapPosn % bigGridDimension) != (bigGridDimension - 1)){
			for (index = blockStartIndex; index< (blockStartIndex + ((gridWidth * gridWidth * bigGridDimension)));index+=(gridWidth * bigGridDimension)){
			
				if (mapGrid[index - 1]==filledWithWater){
					queue.push(index);
				}
			}				
		}
		
		// hacia la derecha
		if ((currMapPosn % bigGridDimension) != 0){
			for (index = (blockStartIndex + gridWidth - 1); 
						index< (blockStartIndex + ((gridWidth * gridWidth * bigGridDimension)));index+=(gridWidth * bigGridDimension)){					
	
				if (mapGrid[index + 1]==filledWithWater){
					queue.push(index);
				}
			}				
		}			
	}
	
	var blockWidthInCells = gridWidth * blockWidth;
	
	// realiza el relleno de inundacion
	while (queue.length>0){
		var currPoint = queue.shift();
		
		var rem1 = currPoint % blockWidthInCells;
		var leftBound = currPoint - rem1;
		var rightBound = leftBound + blockWidthInCells;
		
		// toma el punto actual y se mueve a la izquierda, va revisando cada celda y si tiene "unfilled" la setea a "filledWithWater" para inundarla
		var foundNonFill = 0;
		for (x=currPoint;(x>=leftBound && !foundNonFill);x--){
			if (mapGrid[x]==unfilled){
				mapGrid[x]=filledWithWater;
		
				if ((x+blockWidthInCells<mapGrid.length) && (mapGrid[x + blockWidthInCells]==unfilled)){
						queue.push(x + blockWidthInCells);
				}
				
				if ((x-blockWidthInCells>0) && (mapGrid[x-blockWidthInCells]==unfilled)){
						queue.push(x - blockWidthInCells);
				}
			}
			else if (mapGrid[x]==tooHigh) {
				foundNonFill = 1;
			}
		}
		
		// se mueve a la derecha, va revisando cada celda y si tiene "unfilled" la setea a "filledWithWater" para inundarla
		foundNonFill = 0;
		for (x=currPoint+1;(x<rightBound && !foundNonFill);x++){
		
			if (mapGrid[x]==unfilled){
				results[x]=filledWithWater;
				
				if ((x+blockWidthInCells<mapGrid.length) && (mapGrid[x+blockWidthInCells]==unfilled)){
						queue.push(x + blockWidthInCells);
				}
				
				if ((x-blockWidthInCells>0) && (mapGrid[x-blockWidthInCells]==unfilled)){
						queue.push(x - blockWidthInCells);
				}					
			}
			else if (mapGrid[x]==tooHigh) {
				foundNonFill = 1;
			}
		}
	}	
}

// elimina cualquier marcador que haya en el mapa
function clearMap() 
{     
	for(var i=0; i<this.mapMarkers.length; i++){         
		this.mapMarkers[i].setMap(null);     
	}     
	this.mapMarkers = new Array(); 
}

// convierte de grados a radianes
Math.radians = function(degrees) {
	return degrees * Math.PI / 180;
};

// convierte de radianes a grados
Math.degrees = function(radians) {
	return radians * 180 / Math.PI;
};


//captura el punto (latLong) sobre el cual se hizo click en el mapa para establecer el epicentro, y el angulo  para calcular la direccion en que este se propagara
var mapMouseMove = function(point) {			
	var latDiff = point.latLng.lat() - clickedLocation.lat();
	var lngDiff = point.latLng.lng() - clickedLocation.lng();
	var angle = Math.degrees(Math.atan(lngDiff/latDiff));
	var direction = "XXX";

	// longitud es east/west
	// latitud es north/south
				
	if (latDiff >= 0){ // 1er y 2do cuadrante
		if (angle>-22 && angle<=22){
			clickedAngle = 0;
			direction = "north";
		}
		else if (angle>22 && angle<=67){
			clickedAngle = 45;
			direction = "northeast";
		}
		else if (angle>67 && angle<=112){
			clickedAngle = 90;
			direction = "east";
		}
		else if (angle<-22 && angle>=-67){
			clickedAngle = 315;
			direction = "northwest";
		}
		else if (angle<-67 && angle>=-112){
			clickedAngle = 270;
			direction = "west";
		}
	}
	else{ // 3er y 4to cuadrante
		if (angle>-22 && angle<=22){
			clickedAngle = 180;
			direction = "south";
		}
		else if (angle>22 && angle<=67){
			clickedAngle = 225;
			direction = "southwest";
		}
		else if (angle>67 && angle<=112){
			clickedAngle = 270;
			direction = "west";
		}
		else if (angle<-22 && angle>=-67){
			clickedAngle = 135;
			direction = "southeast";
		}
		else if (angle<-67 && angle>=-112){
			clickedAngle = 90;
			direction = "east";
		}						
	}
	
	if (direction!='XXX'){
		map.setOptions({draggableCursor:'static/images/arrows/arrow-' + direction + '.png), crosshair'});
	}
}

// esta funcion es la que llama el listener cuando se hace el click inicial sobre el mapa
function drawTsunamiMapForEvent(event)
{
	if (!mappingInProgress){
		
		if (initialClickTaken){
			google.maps.event.removeListener(mapMoveListenerHandle);
			map.setOptions({draggableCursor:'crosshair'});
			marker.setMap(null);
			drawTsunamiForLocation(clickedLocation);
			initialClickTaken = 0;
		}
		else {
			// clickedLocation captura la ubicacion (latLong) donde se hizo click
			clickedLocation = event.latLng;

			var image = new google.maps.MarkerImage('static/images/arrows/marker.png',
				new google.maps.Size(30, 30),
				new google.maps.Point(0,0));
				
			//captura la direccion hacia donde se esté moviendo el mouse para establecer la direccion que tendrá la propagación
			var msg = "Ahora haga clic otra vez en la dirección para que el tsunami vaya";
			setOutputMsg(msg);

			marker = new google.maps.Marker({position:clickedLocation,map:map,icon:image,title:"Posición inicial"});

			mapMoveListenerHandle = google.maps.event.addListener(map, 'mousemove', mapMouseMove);
			
			initialClickTaken = 1;
		}
	}
}

// funcion que captura el rango de propagacion, y la altura de ola, y el punto de origen para realizar el proceso de calculo de propagacion y dibujo de esta sobre el mapa
function drawTsunamiForLocation(clickedLocation){
	var range = Math.round(parseFloat(document.getElementById('Range').value)*100)/100;
	var height = Math.round(parseFloat(document.getElementById('WaveHeight').value)*100)/100;
	
	if (mappingInProgress){
		return;
	}
	
	clearMap();

	if (height<1 || height > maxWaveHeight  || !IsNumeric(height)){
		setOutputMsg("La altura de las olas debe estar entre 1 y " + maxWaveHeight + "m.");
	}
	else if (range<10 || range > maxRange || !IsNumeric(range)){
		setOutputMsg("El rango debe estar entre 10km y " + maxRange + "km.");
	}
	else{ // si los parametros de rango de propagacion y altura de ola están bien, entonces llama a la funcion simulateTsunamiPropagation
		mappingInProgress = 1;
		simulateTsunamiPropagation(clickedLocation, -1, -1, null, -1, -1, null, null, -1);			
	}
}

// funcion que resetea el mapa a su estado inicial y permite realizar una nueva simulacion
function reDraw(){	
	drawTsunamiForLocation(currLocation);
}


// funcion que dibuja toda la malla de propagacion sobre el mapa
function drawFillGridMap(mapGrid, locationGrid, direction, printedGrid){
	sectorColor = "#509f64"; //#4d4dff
	
	var polyLine = new Array();
	var allFilled = 1;
	
	// Polygon es una herramienta de dibujo provista por google maps
	var polyOptions = {
		geodesic:true,
		clickable:false,
		fillColor:sectorColor,
		fillOpacity:0.65,
		strokeColor:sectorColor,
		strokeOpacity:0
	};
	
	var index = 0;
	for (index = 0; index<mapGrid.length;index++){
		// al encontrar una celda "filledWithWater" va a dibujarla
		if (mapGrid[index]==filledWithWater && printedGrid[index]==0){
		
			polyLine[index] = new google.maps.Polygon(polyOptions);
			var polyCoords = new Array(0);
			
			var index2 = 0;
			var currAngle = parseInt(direction) + 45;
			for (index2=0;index2<=4; index2++){
				if (currAngle>=360) currAngle-=360;
			
				if (index2==0 || index2==4 || index2==3){
					// Izquierda superior e inferior
					// calcula las coordenadas del poligono
					polyCoords[index2] = google.maps.geometry.spherical.computeOffset(locationGrid[index], 
						gridSector * 0.707106, currAngle);
				
				}
				else if (index2==1){
					// Arriba a la derecha
					if (index <= (bigGridDimension * gridHeight)){ 
						// calcula las coordenadas del poligono
						polyCoords[index2] = google.maps.geometry.spherical.computeOffset(locationGrid[index], 
							gridSector * 0.707106, currAngle);
					}
					else{
						var tmpAngle = currAngle - 90;
						if (tmpAngle<360) tmpAngle = tmpAngle + 360;
						// calcula las coordenadas del poligono
						polyCoords[index2] = google.maps.geometry.spherical.computeOffset(locationGrid[index-(bigGridDimension * gridHeight)], 
							gridSector * 0.707106, tmpAngle);
					}
				}
				else if (index2==2){
					// abajo a la derecha
					if (index <= (bigGridDimension * gridHeight)){ 
						// calcula las coordenadas del poligono
						polyCoords[index2] = google.maps.geometry.spherical.computeOffset(locationGrid[index], 
							gridSector * 0.707106, currAngle);
					}
					else{
						var tmpAngle = currAngle + 90;
						if (tmpAngle>360) tmpAngle = tmpAngle - 360;
						// calcula las coordenadas del poligono
						polyCoords[index2] = google.maps.geometry.spherical.computeOffset(locationGrid[index-(bigGridDimension * gridHeight)], 
							gridSector * 0.707106, tmpAngle);
					}
				}

				currAngle+=90;
			}
			
			// dibuja el poligono completo de la malla
			polyLine[index].setPath(polyCoords);
			polyLine[index].setMap(map);
			mapMarkers.push(polyLine[index]);
			printedGrid[index] = 1;
		}
		else{
			allFilled = 0;
		}
	}
	
	return allFilled;
}

// funcion que realiza la simulacion de propagacion y dibujo de esta sobre el mapa	
function simulateTsunamiPropagation(clickedLocation, angle, waveHeight, mapGrid, currMapPosn, origAngle, locationGrid, printedGrid, range)
{
	var locations = [];

	if (mapGrid == null){
		currLocation = clickedLocation;
		mapGrid = new Array(bigGridDimension * bigGridDimension * gridWidth * gridWidth);
		locationGrid = new Array(bigGridDimension * bigGridDimension * gridWidth * gridWidth);
		printedGrid = new Array(bigGridDimension * bigGridDimension * gridWidth * gridWidth);
		var x = 0
		for (x=0; x< (blockWidth * blockWidth) * (gridWidth * gridWidth); x++){
			mapGrid[x] = notMapped;
			locationGrid[x] = 0;
			printedGrid[x] = 0;
		}
		
		currMapPosn = blockCenter;
	}
	
	if (angle == -1){
		angle = clickedAngle;
	}
	
	if (origAngle == -1){
		origAngle = angle;
	}
	
	if (waveHeight == -1){
		waveHeight = Math.round(parseFloat(document.getElementById('WaveHeight').value)*100)/100;
	}
	
	if (range == -1){
		range = Math.round(parseFloat(document.getElementById('Range').value)*100)/100;
	}
	
	if (range!=null){
		gridSector = (Math.round(parseFloat(range*1000)*100)/100) / 50;
	}
	
	// locations será la malla de propagacion tomando como parametros un angulo de direccion y nuestra posicion de origen(latLong)
	locations = getSpreadLocations(angle, clickedLocation);

	// Crea un objeto LocationElevationRequest usando el valor de la matriz locations
	var positionalRequest = {'locations': locations};

	
	// Inicia la solicitud de elevacion para la ubicacion
	elevator.getElevationForLocations(positionalRequest, function(results, status)
	{
		if (status == google.maps.ElevationStatus.OK)
		{
			// si recibe un resultado, solicita que se evalue si el punto donde se encuentra será inundado a no
			mapResultsToMapGrid(mapGrid, locationGrid, currMapPosn, results, waveHeight, locations);
			// realiza la inundacion
			performFloodFill(mapGrid, currMapPosn);
			
			// Retrieve the first result
			if (results[originIndex].elevation.toFixed(3)<1 || currMapPosn!=blockCenter)
			{
				if (results[0])
				{
					var completionStatus = getCompletionStatus(mapGrid);
					
					// dibuja toda la malla de propagacion sobre el mapa						
					drawFillGridMap(mapGrid, locationGrid, angle, printedGrid);
					
					// si al terminar de hacer y dibujar la propagación (dentro del rango de propagacion establecido) el tsunami no llega a tierra, muestra un mensaje
					if (completionStatus==COMPLETE_ALL_WATER){
						setOutputMsg("Este tsunami no llegó a tierra.");
						mappingInProgress = 0;
					}
					// cuando termina de simular la propagacion, y el tsunami llego a tierra, permite dibujar el área afectada
					else if (completionStatus==COMPLETE_MIXED){
						mappingInProgress = 0;		
						var reDrawButton = document.getElementById("reDraw");
						var drawAreaButton = document.getElementById("drawArea");
						var resetAreaButton = document.getElementById("resetArea");
						reDrawButton.style.display = "block";
						drawAreaButton.style.visibility= "visible";
						resetAreaButton.style.visibility= "visible";
					}
					
					// ejecucion normal que se da al hacer clic sobre el punto de inicio y marcar una direccion de propagacion
					if (currMapPosn == blockCenter){
						var marker=placeMarker(clickedLocation, results[0].elevation.toFixed(3) + " m", angle);
						marker.setMap(map);
						mapMarkers.push(marker);
					
						var url = "lng=" + 
							clickedLocation.lng().toFixed(4) + "&lat=" + clickedLocation.lat().toFixed(4) +
							"&dir=" + angle + "&hgt=" + waveHeight + "&rng=" + document.getElementById('Range').value;
						console.log("clickedLocation: " + url);
							
						var msg = " <a href=" + + " class=sharelink>" +  + "</a>";
						setOutputMsg(msg);
						
						map.setCenter(clickedLocation);
					}
					
					// hace la verificacion si puede propagarse hacia la izquierda
					if (canSpreadToLeft(mapGrid, currMapPosn)){
						var leftAngle = leftAngle = parseInt(origAngle) - 90;
						var leftStartPoint = google.maps.geometry.spherical.computeOffset(clickedLocation, gridSector * 10, 
									leftAngle);
						var leftMapPosn = currMapPosn - 1;
					
						setTimeout(
							function(){
								simulateTsunamiPropagation(leftStartPoint, origAngle, waveHeight, mapGrid, leftMapPosn, origAngle, locationGrid, printedGrid,
										range);
							}, nextCallTime + 1500);
					}
					
					// hace la verificacion si puede propagarse hacia la derecha
					if (canSpreadToRight(mapGrid, currMapPosn)){
						var rightMapPosn = currMapPosn + 1;
						var rightAngle = parseInt(origAngle) + 90;
						if (rightAngle>360) rightAngle -= 360; 

						var rightStartPoint = google.maps.geometry.spherical.computeOffset(clickedLocation, gridSector * 10, 
								rightAngle);
						setTimeout(
							function(){
								simulateTsunamiPropagation(rightStartPoint, origAngle, waveHeight, mapGrid, rightMapPosn, origAngle, locationGrid, printedGrid,
									range);
							}, nextCallTime + 750);
					}
					
					// hace la verificacion si puede propagarse hacia arriba
					if (canSpreadToUp(mapGrid, currMapPosn)){
						var upStartPoint = google.maps.geometry.spherical.computeOffset(clickedLocation, gridSector * 10, 
								angle);
						var upMapPosn = currMapPosn + blockWidth;
						setTimeout(
							function(){
								simulateTsunamiPropagation(upStartPoint, angle, waveHeight, mapGrid, upMapPosn, origAngle, locationGrid, printedGrid,
									range);
							}, nextCallTime);
					}
				}
				else
				{
					setOutputMsg("Sin resultados");
					mappingInProgress = 0;
				}
			}
			else{
				// El epicentro debe fijarse sobre el nivel del mar
				setOutputMsg("La elevación del punto de partida es de " + results[originIndex].elevation.toFixed(3) + " m. Un tsunami debe comenzar en el océano.");
				
				var marker=placeMarker(clickedLocation,results[0].elevation.toFixed(3) + " m", -1);
				marker.setMap(map);
				mapMarkers.push(marker);
				mappingInProgress = 0;
				
				//si el epicentro lo señalan el algun punto sobre tierra, se intenta calcular un mejor punto sobre el nivel del mar
				drawMapForInlandLocation(clickedLocation, waveHeight, range);
			}
		}
		else
		{
			setOutputMsg("El servicio de elevación falló debido a: " + status);
			mappingInProgress = 0;
			
		}
	});
}

// funcion que calcula un mejor punto de origen, si el punto inicial fue fijado en tierra
function drawMapForInlandLocation(origLocation, waveHeight, range){
	// determina 8 puntos de partida potenciales a partir del punto inicial
	var index = 0;
	var currAngle = 0;
	var startingLocations = [];
	for (index = 0; index<8;index++){
		var currStartPoint = google.maps.geometry.spherical.computeOffset(origLocation, range * 1000 * 0.65 , 
				currAngle);
		currAngle = currAngle + 45;
		startingLocations.push(currStartPoint);
	}
	
	var positionalRequest = {'locations': startingLocations};
			
	// Initiate the location request
	// inicia la solicitud de elevacion para cada una de las ubicaciones potenciales
	elevator.getElevationForLocations(positionalRequest, function(results, status)
	{
		if (status == google.maps.ElevationStatus.OK)
		{
			// loop through till find one point under water
			//realiza el ciclo hasta que encuentra un punto que se encuentre debajo del nivel del mar
			index = 0;
			var found = 0;
			var startPos = null;
			currAngle = 0;
			
			while (index<8 && !found){
				if (getElev(results, index)<0){
					found = 1;
					startPos = startingLocations[index];
				}
				else{
					index = index + 2;
					currAngle = currAngle + 90;
				}
			}
			
			if (!found){
				index = 1;
				currAngle = 45;
				
				while (index<8 && !found){
					if (getElev(results, index)<0){
						found = 1;
						startPos = startingLocations[index];
					}
					else{
						index = index + 2;
						currAngle = currAngle + 90;
					}
				}
			}
			
			if (found){
				// al encontrar un buen punto inicial, realiza la simulacion de propagacion a partir de ese punto
				var tsuAngle = currAngle + 180;
				if (tsuAngle>360) tsuAngle = tsuAngle -360;
				
				simulateTsunamiPropagation(startPos, tsuAngle, waveHeight, null, -1, -1, null, null, range);
			}
		}
		else{
			setOutputMsg("Elevation service failed due to: " + status);
		}
	});
}

// funcion que toma la direccion de propagación, y en base a ella, crea un marcador con la flecha correspondiente
function placeMarker(location,text,direction)
{
	var imagename = '';
	if (direction == -1){
		imagename = 'marker';
	}
	else if (direction<=22 || direction>338){
		imagename = 'arrow-north';
	}
	else if (direction>22 && direction<=67){
		imagename = 'arrow-northeast';
	}
	else if (direction>67 && direction<=112){
		imagename = 'arrow-east';
	}
	else if (direction>112 && direction<=157){
		imagename = 'arrow-southeast';
	}
	else if (direction>157 && direction<=202){
		imagename = 'arrow-south';
	}
	else if (direction>202 && direction<=247){
		imagename = 'arrow-southwest';
	}
	else if (direction>247 && direction<=292){
		imagename = 'arrow-west';
	}
	else if (direction>292 && direction<=339){
		imagename = 'arrow-northwest';
	}

	var imageUrl = 'static/images/arrows/' + imagename + '.png';
		
	var image = new google.maps.MarkerImage(imageUrl,
		new google.maps.Size(35, 35),
		new google.maps.Point(0,0));

	var marker = new google.maps.Marker({position:location,map:map,icon:image,title:text});

	return marker;
}


// establece la flecha que llevará el cursor para determinar la direccion de propagación
function setCursor(direction){
	
	if (direction == 0){
		map.setOptions({draggableCursor:'crosshair'});
	}
	else if (direction == 1){
		map.setOptions({draggableCursor:'url(static/images/arrows/arrow-north.png), crosshair'});
	}
	else if (direction == 2){
		map.setOptions({draggableCursor:'url(static/images/arrows/arrow-northeast.png), crosshair'});
	}
	else if (direction == 3){
		map.setOptions({draggableCursor:'url(static/images/arrows/arrow-east.png), crosshair'});
	}
	else if (direction == 4){
		map.setOptions({draggableCursor:'url(static/images/arrows/arrow-southeast.png), crosshair'});
	}
	else if (direction == 5){
		map.setOptions({draggableCursor:'url(static/images/arrows/arrow-south.png), crosshair'});
	}
	else if (direction == 6){
		map.setOptions({draggableCursor:'url(static/images/arrows/arrow-southwest.png), crosshair'});
	}
	else if (direction == 7){
		map.setOptions({draggableCursor:'url(static/images/arrows/arrow-west.png), crosshair'});
	}
	else if (direction == 8){
		map.setOptions({draggableCursor:'url(static/images/arrows/arrow-northwest.png), crosshair'});
	}
}

// funcion que toma los valores de la escala de Imamura que selecciono el usuario
function setSizeParamsFromDropDown(selection){	
	document.getElementById('WaveHeight').value = waveSizeArr[selection];
	document.getElementById('Range').value = waveRangeArr[selection];
	document.getElementById('wave-height-p').textContent=waveSizeArr[selection];
}


function drawArea() {
	google.maps.event.removeListener(firstClickTakenListenerHandle);
	map.setOptions({draggableCursor:'crosshair'});
	google.maps.event.addListener(map, "click", function(evt) {
		//Cuando se haga click sobre el mapa, pasar el objeto LatLng a la funcion measureAdd
		measureAdd(evt.latLng);
	});
}

// esta funcion esta basada en el codigo de https://web.archive.org/web/20130708035754/http://geojason.info:80/demos/line-length-polygon-area-google-maps-v3/
function measureAdd(latLng) {

	//agregar al mapa un marcador que sea draggable donde el usuario hizo click
	var marker = new google.maps.Marker({
		map: map,
		position: latLng,
		draggable: true,
		raiseOnDrag: false,
		title: "Drag me to change shape",
		icon: new google.maps.MarkerImage("static/images/arrows/circled-dot.png", 
											new google.maps.Size(9,9), 
											new google.maps.Point(0,0), 
											new google.maps.Point(5,5)
		)
	});

	//agregar el parametro latLng a la linea MVCArray y al polígono MVCArray
	//los objetos añadidos a estos MVCArrays automaticamente actualizan las formas de la linea y el poligono en el mapa
	measure.mvcLine.push(latLng);
	measure.mvcPolygon.push(latLng);

	//añadir este marcador a un MVCArray
	//de esta forma, luego se podra hacer un loop sobre el array y removerlos cuando se haya terminado de medir
	measure.mvcMarkers.push(marker);

	//obtiene la posicion del latLng que se acaba de pushear en el MVCArray
	//esto se necesitara luego para actualizar el MVCArray si el usuario mueve los vertices
	var latLngIndex = measure.mvcLine.getLength()-1;

	//cuando el usuario hace hover sobre un vertice, cambia la forma y el color para que se note que se puede mover
	google.maps.event.addListener(marker, "mouseover", function() {
		marker.setIcon(new google.maps.MarkerImage("static/images/arrows/circled-dot-hover.png", 
													new google.maps.Size(15,15), 
													new google.maps.Point(0,0), 
													new google.maps.Point(8,8)
		));
	});

	//cuando el usuario quita el hover, regresa el marcador inicial
	google.maps.event.addListener(marker, "mouseout", function() {
		marker.setIcon(new google.maps.MarkerImage("static/images/arrows/circled-dot.png", 
													new google.maps.Size(9,9), 
													new google.maps.Point(0,0), 
													new google.maps.Point(5,5)
		));
	});

	//cuando los vertices son movidos, se actualiza la geometria de 
	//la linea y el poligono al resetear el objeto latLng en esa posicion
	google.maps.event.addListener(marker, "drag", function(evt) {
		measure.mvcLine.setAt(latLngIndex, evt.latLng);
		measure.mvcPolygon.setAt(latLngIndex, evt.latLng);
	});

	//cuando se haya terminado de arrastrar el vertice y hay mas de un vertice
	//mide y calcula la longitud y el area
	google.maps.event.addListener(marker, "dragend", function() {
		if (measure.mvcLine.getLength() > 1) {
			measureCalc();
		}
	});

	//si hay mas de un vertice en la linea
	if(measure.mvcLine.getLength() > 1){

		//Si aun no se ha creado la linea
		if (!measure.line) {

			//dibuja la linea (google.maps.Polyline)
			measure.line = new google.maps.Polyline({
				map: map,
				clickable: false,
				strokeColor: "#FF0000",
				strokeOpacity: 1,
				strokeWeight: 3,
				path: measure.mvcLine
			});
		}

		//si hay mas de dos vertices, entonces es un poligono
		if(measure.mvcPolygon.getLength() > 2) {

			//si aun no se ha creado el poligono
			if (!measure.polygon) {

				//dibuja el poligono (google.maps.Polygon)
				measure.polygon = new google.maps.Polygon({
					clickable: false,
					map: map,
					fillOpacity: 0.25,
					strokeOpacity: 0,
					paths: measure.mvcPolygon
				});
			}
		}
	}

	//si hay mas de un vertice, mide la longitud y calcula el area
	if(measure.mvcLine.getLength() > 1){
		measureCalc();
	}
}

//esta funcion calcula la longitud y area actual con la ayuda 
//de la libreria geometry de Google Maps
function measureCalc() {
	//usa la libreria geometry de Google Maps para medir la longitud de la linea
	var length  = google.maps.geometry.spherical.computeLength(measure.line.getPath());
	console.log("Longitud: " + length);
	length = length.toFixed(2);
	document.getElementById("span-length").textContent=length + " m.";
	
	//Si hay mas de dos vertices, entonces se tiene un poligono
	if (measure.mvcPolygon.getLength() > 2) {
		//usa la libreria geometry de Google Maps para medir el area del poligono
		var area = google.maps.geometry.spherical.computeArea(measure.polygon.getPath());
		console.log("Área: " + area);
		area = (area/1000000).toFixed(2);
		document.getElementById("span-area").textContent=area + " km2.";		
	}
}

//esta funcion se asign a un boton  para reinicializar los objetos de medicion y 
//resetear los valores a 0
function measureReset() {
	//si se tiene un poligono o una linea, quitarlos del mapa y setearlos a null
	if(measure.polygon) {
		measure.polygon.setMap(null);
		measure.polygon = null;
	}
	if(measure.line) {
		measure.line.setMap(null);
		measure.line = null;
	}

	//vaciar los MVCArrays de mvcLine y mvcPolygon
	measure.mvcLine.clear();
	measure.mvcPolygon.clear();

	//hacer un ciclo a traves de los marcadores MVCArray y remover cada uno del mapa
	//luego vaciar el array mvcMarkers
	measure.mvcMarkers.forEach(function(elem,index) {
		elem.setMap(null);
	});
	measure.mvcMarkers.clear();

	document.getElementById("span-length").textContent="";
	document.getElementById("span-area").textContent="";
}
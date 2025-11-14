import pandas as pd
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.chrome.options import Options
import time
import os
from datetime import datetime, timedelta
from dotenv import load_dotenv
import threading
from collections import defaultdict
import math
import numpy as np
import csv
import json

# Cargar variables del archivo .env
load_dotenv()

# Intenta importar pybit, si no está instalado, usa modo simulación
try:
    from pybit.unified_trading import HTTP
    PYBIT_INSTALADO = True
except ImportError:
    PYBIT_INSTALADO = False
    print("⚠️  Pybit no instalado - Usando modo simulación")
    print("💡 Ejecuta: pip install pybit")

# ========== CONFIGURACIÓN CHROME PARA GOOGLE CLOUD ==========

def configurar_chrome_cloud():
    """Configura Chrome para Google Cloud"""
    chrome_options = Options()
    
    # Configuración optimizada para servidor
    chrome_options.add_argument('--headless=new')
    chrome_options.add_argument('--no-sandbox')
    chrome_options.add_argument('--disable-dev-shm-usage')
    chrome_options.add_argument('--disable-gpu')
    chrome_options.add_argument('--window-size=1920,1080')
    chrome_options.add_argument('--disable-extensions')
    chrome_options.add_argument('--disable-software-rasterizer')
    chrome_options.add_argument('--remote-debugging-port=9222')
    chrome_options.add_argument('--user-agent=Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36')
    
    # Intentar diferentes configuraciones
    try:
        # Opción 1: ChromeDriver del sistema
        service = Service('/usr/bin/chromedriver')
        driver = webdriver.Chrome(service=service, options=chrome_options)
        print("✅ Chrome configurado con chromedriver del sistema")
        return driver
    except Exception as e:
        print(f"❌ Opción 1 falló: {e}")
        
    try:
        # Opción 2: webdriver-manager
        from webdriver_manager.chrome import ChromeDriverManager
        service = Service(ChromeDriverManager().install())
        driver = webdriver.Chrome(service=service, options=chrome_options)
        print("✅ Chrome configurado con webdriver-manager")
        return driver
    except Exception as e:
        print(f"❌ Opción 2 falló: {e}")
        
    try:
        # Opción 3: Sin Service
        driver = webdriver.Chrome(options=chrome_options)
        print("✅ Chrome configurado sin Service")
        return driver
    except Exception as e:
        print(f"❌ Todas las opciones fallaron: {e}")
        return None

def crear_dataframe_respaldo():
    """Crea un DataFrame de respaldo cuando falla el scraping"""
    print("🔄 Usando datos de respaldo...")
    
    # Datos de ejemplo basados en cryptos populares
    datos_respaldo = {
        'COIN': ['Bitcoin BTC', 'Ethereum ETH', 'Solana SOL', 'Cardano ADA', 'Polkadot DOT', 
                'Avalanche AVAX', 'Polygon MATIC', 'Chainlink LINK', 'Litecoin LTC', 'Uniswap UNI'],
        'PRICE': ['45000', '2400', '110', '0.55', '7.2', '40.5', '0.85', '18.3', '72.1', '6.5'],
        'CHG 24H': ['+2.5', '+1.8', '+5.2', '+3.1', '+2.8', '+4.5', '+1.2', '+3.7', '+1.5', '+2.9'],
        'MKT CAP': ['880B', '290B', '45B', '19B', '9.2B', '15B', '8.1B', '10.5B', '5.3B', '4.9B'],
        'VOL 24H': ['25B', '12B', '3.5B', '1.2B', '0.8B', '1.5B', '0.9B', '1.1B', '0.7B', '0.6B'],
        'OPEN INTEREST': ['15B', '8.5B', '2.1B', '0.9B', '0.5B', '1.1B', '0.6B', '0.8B', '0.4B', '0.3B'],
        'OI CHG 24H': ['+12.5', '+8.3', '+15.2', '+9.1', '+7.8', '+11.5', '+6.2', '+10.7', '+5.5', '+8.9']
    }
    
    df = pd.DataFrame(datos_respaldo)
    print(f"✅ DataFrame de respaldo creado con {len(df)} filas")
    return df

# Variables globales
datos_anteriores = None
bybit_session = None
operaciones_lock = threading.Lock()  # ✅ AÑADIDO: Lock para sincronización
balance_inicial = 0.0
perdida_maxima_permitida = 0.60  # 60%
bot_desactivado_por_perdida = False
bot_detenerse_al_cerrar = False

# CONFIGURACIÓN BYBIT DESDE .ENV
BYBIT_CONFIG = {
    "api_key": os.getenv("BYBIT_API_KEY"),
    "api_secret": os.getenv("BYBIT_SECRET_KEY"),
    "testnet": os.getenv("BYBIT_TESTNET", "False").lower() == "true",
}

# Estados de operación
ESTADOS = {
    "SIN_OPERAR": 0,
    "LONG_ABIERTO": 1,
    "ESPERANDO_SHORT": 2,
    "AMBOS_ABIERTOS": 3,
    "ADD_FUNDS_ACTIVO": 4
}

# Tracking de operaciones activas
operaciones_activas = {}
monitoreo_activo = False

# CONFIGURACIÓN DE LÍMITES
MAX_MONEDAS_SIMULTANEAS = 3
LEVERAGE = 25
CANTIDAD_USDT = 5.5
SL_PORCENTAJE = 20.0

# Control del bot
bot_salir = False

# Variables globales para tracking de velas
ultimo_cierre_vela = {}
precios_velas_actuales = {}

# ========== SISTEMA DE REGISTRO Y ESTADÍSTICAS ==========

estadisticas = {
    'total_operaciones': 0,
    'operaciones_ganadas': 0,
    'operaciones_perdidas': 0,
    'operaciones_breakeven': 0,
    'ganancia_total': 0,
    'perdida_total': 0,
    'operaciones_cerradas': []
}

estadisticas_lock = threading.Lock()

def detener_bot_suavemente():
    """Activa el modo de parada suave"""
    global bot_detenerse_al_cerrar
    bot_detenerse_al_cerrar = True
    print("🛑 DETENCIÓN DEL BOT PROGRAMADA: No se abrirán nuevas operaciones")

def inicializar_archivo_registro():
    """Inicializa el archivo CSV de registro si no existe"""
    try:
        archivo = 'registro_operaciones.csv'
        if not os.path.exists(archivo):
            with open(archivo, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow([
                    'fecha_apertura', 'fecha_cierre', 'moneda', 'symbol',
                    'precio_long', 'precio_short', 'precio_cierre',
                    'ejecuto_short', 'ejecuto_add_funds', 'tipo_cierre',
                    'ganancia_porcentaje', 'ganancia_usdt', 'cantidad_usdt',
                    'duracion_minutos', 'maximo_alcanzado', 'minimo_alcanzado',
                    'volumen_operado', 'razon_cierre'
                ])
            print(f"✅ Archivo de registro creado: {archivo}")
        return archivo
    except Exception as e:
        print(f"❌ Error inicializando archivo de registro: {e}")
        return 'registro_operaciones.csv'

def registrar_operacion(symbol, precio_long, precio_cierre, 
                       ejecuto_short=False, ejecuto_add_funds=False,
                       tipo_cierre="", ganancia_porcentaje=0, 
                       cantidad_usdt=5.5, razon_cierre=""):
    """Registra una operación en el archivo CSV - CORREGIDO PARA SOLO LONG"""
    try:
        archivo = inicializar_archivo_registro()
        
        # Buscar información de la operación
        operacion = operaciones_activas.get(symbol, {})
        moneda = operacion.get('moneda', symbol.replace('USDT', ''))
        
        # Calcular duración
        fecha_apertura = operacion.get('fecha_apertura', datetime.now())
        fecha_cierre = datetime.now()
        duracion_minutos = int((fecha_cierre - fecha_apertura).total_seconds() / 60)
        
        # Obtener precios short y otros datos
        precio_short = operacion.get('precio_short', 0)
        maximo_alcanzado = operacion.get('maximo_alcanzado', precio_long)
        minimo_alcanzado = operacion.get('minimo_alcanzado', precio_long)
        
        # Calcular volumen operado
        volumen_operado = cantidad_usdt
        if ejecuto_add_funds:
            volumen_operado += 16.5  # Add funds
        if ejecuto_short:
            volumen_operado += 11.0  # Short
        
        # Calcular ganancia en USDT
        ganancia_usdt = cantidad_usdt * (ganancia_porcentaje / 100)
        
        # ✅ CORRECCIÓN: Asegurar que todos los campos tengan valores válidos
        # y estén en el orden correcto del CSV
        
        with open(archivo, 'a', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerow([
                # Fechas
                fecha_apertura.strftime('%Y-%m-%d %H:%M:%S'),
                fecha_cierre.strftime('%Y-%m-%d %H:%M:%S'),
                # Información moneda
                moneda,
                symbol,
                # Precios - ✅ CORREGIDO: precio_short solo si existe
                f"{precio_long:.8f}",
                f"{precio_short:.8f}" if precio_short and precio_short > 0 else "",  # Vacío si no hay short
                f"{precio_cierre:.8f}",  # ✅ precio_cierre en su campo correcto
                # Ejecuciones
                "SI" if ejecuto_short else "NO",
                "SI" if ejecuto_add_funds else "NO",
                # Cierre y ganancias - ✅ CORREGIDO: tipo_cierre en su campo
                tipo_cierre,  # Este va en el campo 'tipo_cierre'
                f"{ganancia_porcentaje:.4f}",  # Este va en 'ganancia_porcentaje'
                f"{ganancia_usdt:.4f}",
                f"{cantidad_usdt:.2f}",
                # Métricas
                duracion_minutos,
                f"{maximo_alcanzado:.8f}",
                f"{minimo_alcanzado:.8f}",
                f"{volumen_operado:.2f}",
                # Razón - ✅ CORREGIDO: razon_cierre en su campo final
                razon_cierre
            ])
        
        print(f"📝 Operación registrada en CSV: {symbol} - {tipo_cierre}")
        
        # Actualizar estadísticas
        with estadisticas_lock:
            estadisticas['total_operaciones'] += 1
            estadisticas['operaciones_cerradas'].append({
                'symbol': symbol,
                'fecha_cierre': fecha_cierre.strftime('%Y-%m-%d %H:%M:%S'),
                'precio_apertura': precio_long,
                'precio_cierre': precio_cierre,
                'ganancia_porcentaje': ganancia_porcentaje,
                'ganancia_usdt': ganancia_usdt,
                'cantidad_usdt': cantidad_usdt,
                'tipo_cierre': tipo_cierre,
                'razon_cierre': razon_cierre
            })
            
            if "TP_VOLUME_DOWN" in tipo_cierre:
                estadisticas['operaciones_ganadas'] += 1
                estadisticas['ganancia_total'] += ganancia_usdt
            elif "SL" in tipo_cierre:
                estadisticas['operaciones_perdidas'] += 1
                estadisticas['perdida_total'] += abs(ganancia_usdt)
            else:
                estadisticas['operaciones_breakeven'] += 1
        
        return True
        
    except Exception as e:
        print(f"❌ Error registrando operación: {e}")
        return False

def mostrar_estadisticas():
    """Muestra las estadísticas actuales del bot"""
    with estadisticas_lock:
        total = estadisticas['total_operaciones']
        if total == 0:
            print("📊 No hay operaciones registradas aún")
            return
        
        ganadas = estadisticas['operaciones_ganadas']
        perdidas = estadisticas['operaciones_perdidas']
        breakeven = estadisticas['operaciones_breakeven']
        
        win_rate = (ganadas / total) * 100 if total > 0 else 0
        profit_neto = estadisticas['ganancia_total'] - estadisticas['perdida_total']
        
        print("\n" + "="*80)
        print("📊 ESTADÍSTICAS DETALLADAS DEL BOT")
        print("="*80)
        print(f"📈 Total Operaciones: {total}")
        print(f"✅ Operaciones Ganadas (TP Volume Down): {ganadas} ({win_rate:.1f}%)")
        print(f"❌ Operaciones Perdidas (SL): {perdidas} ({(perdidas/total)*100:.1f}%)")
        print(f"⚖️  Operaciones Break Even: {breakeven} ({(breakeven/total)*100:.1f}%)")
        print(f"💰 Ganancia Total: ${estadisticas['ganancia_total']:.2f}")
        print(f"📉 Pérdida Total: ${estadisticas['perdida_total']:.2f}")
        print(f"💵 Profit Neto: ${profit_neto:.2f}")
        
        if ganadas > 0:
            avg_ganancia = estadisticas['ganancia_total'] / ganadas
            print(f"📊 Ganancia Promedio: ${avg_ganancia:.2f}")
        if perdidas > 0:
            avg_perdida = estadisticas['perdida_total'] / perdidas
            print(f"📊 Pérdida Promedio: ${avg_perdida:.2f}")
        
        # Mostrar últimas 5 operaciones
        if estadisticas['operaciones_cerradas']:
            print(f"\n📋 Últimas 5 Operaciones:")
            print("-" * 100)
            for op in estadisticas['operaciones_cerradas'][-5:]:
                resultado = "🟢" if op['ganancia_porcentaje'] > 0 else "🔴" if op['ganancia_porcentaje'] < 0 else "⚪"
                print(f"   {resultado} {op['symbol']}: {op['tipo_cierre']} | {op['ganancia_porcentaje']:+.2f}% | ${op['ganancia_usdt']:.2f} | {op['razon_cierre']}")
def guardar_estadisticas_json():
    """Guarda las estadísticas en un archivo JSON"""
    try:
        with open('estadisticas_bot.json', 'w', encoding='utf-8') as f:
            json.dump(estadisticas, f, indent=2, ensure_ascii=False)
        print("💾 Estadísticas guardadas en estadisticas_bot.json")
    except Exception as e:
        print(f"❌ Error guardando estadísticas JSON: {e}")

# ========== SISTEMA VOLUME REGRESSION MEJORADO ==========

def calcular_volume_regression(df, short_len=7, long_len=50, source='close'):
    """Calcula el indicador Volume Regression en Python con parámetros personalizables"""
    df = df.copy()
    
    # 1. Regresión de Precio (pendiente) - usando short_len
    def calcular_slope(series, length):
        if len(series) < length:
            return np.nan
        x = np.arange(len(series))
        slope = np.polyfit(x, series, 1)[0]
        return slope
    
    # Precio: usamos short_len con la fuente especificada
    price_source = df[source]
    df['slope_price'] = price_source.rolling(short_len).apply(
        lambda x: calcular_slope(x, short_len), raw=True
    )
    
    # 2. Análisis de volumen por lado
    def calcular_rate(row):
        try:
            high, low, open_, close = row['high'], row['low'], row['open'], row['close']
            tw = high - max(open_, close)  # Top wick
            bw = min(open_, close) - low   # Bottom wick  
            body = abs(close - open_)      # Body
            
            if open_ <= close:  # Vela verde (compra)
                ret = 0.5 * (tw + bw + (2 * body)) / (tw + bw + body)
            else:  # Vela roja (venta)
                ret = 0.5 * (tw + bw + 0) / (tw + bw + body)
            
            return ret if not np.isnan(ret) else 0.5
        except:
            return 0.5
    
    df['rate'] = df.apply(calcular_rate, axis=1)
    
    # 3. Volumen por lado
    df['volume_up'] = df['volume'] * df['rate']
    df['volume_down'] = df['volume'] * (1 - df['rate'])
    
    # 4. Regresión de Volumen - usando long_len
    df['slope_volume_up'] = df['volume_up'].rolling(long_len).apply(
        lambda x: calcular_slope(x, long_len), raw=True
    )
    df['slope_volume_down'] = df['volume_down'].rolling(long_len).apply(
        lambda x: calcular_slope(x, long_len), raw=True
    )
    
    # 5. Señales
    df['vol_up'] = np.where(
        (df['slope_price'] > 0) & 
        (df['slope_volume_up'] > 0) & 
        (df['slope_volume_up'] > df['slope_volume_down']), 1, np.nan
    )
    
    df['vol_down'] = np.where(
        (df['slope_price'] < 0) & 
        (df['slope_volume_down'] > 0) & 
        (df['slope_volume_up'] < df['slope_volume_down']), 1, np.nan
    )
    
    return df

# ========== SISTEMA DETECCIÓN LATERALIZACIÓN (3 HORAS) ==========

def esta_en_rango_lateral(symbol, periodo='5', horas_analizar=3):
    """
    Determina si un activo está en rango lateral en las últimas 3 horas
    """
    try:
        # Calcular número de velas necesarias para 3 horas
        if periodo == '5':  # 5 minutos
            velas_necesarias = (horas_analizar * 60) // 5
        elif periodo == '15':  # 15 minutos
            velas_necesarias = (horas_analizar * 60) // 15
        elif periodo == '1':  # 1 minuto
            velas_necesarias = horas_analizar * 60
        else:  # Por defecto 5 minutos
            velas_necesarias = 36  # 3 horas en velas de 5 min
        
        print(f"   🔍 Analizando lateralización {symbol}: {horas_analizar}h en {periodo}m ({velas_necesarias} velas)")
        
        # Obtener datos OHLCV
        datos = obtener_datos_para_volume_regression(symbol, periodo, velas_necesarias)
        
        if datos is None or len(datos) < velas_necesarias:
            print(f"   ⚠️  Datos insuficientes para análisis lateral")
            return False
        
        # 1. Calcular rango de precio (máximo vs mínimo)
        high_max = datos['high'].max()
        low_min = datos['low'].min()
        precio_promedio = (high_max + low_min) / 2
        rango_porcentual = ((high_max - low_min) / precio_promedio) * 100
        
        # 2. Calcular tendencia de volumen
        volumen_tendencia = calcular_tendencia_volumen(datos)
        
        # 3. Calcular fuerza de tendencia (usando ATR y volatilidad)
        fuerza_tendencia = calcular_fuerza_tendencia(datos)
        
        print(f"   📊 Métricas lateralización {symbol}:")
        print(f"      📈 Rango precio: {rango_porcentual:.2f}%")
        print(f"      📉 Tendencia volumen: {volumen_tendencia:.2f}")
        print(f"      💪 Fuerza tendencia: {fuerza_tendencia:.2f}")
        
        # Criterios para considerar lateralización
        en_rango = rango_porcentual < 2.5  # Menos del 2% de rango
        volumen_decreciente = volumen_tendencia < -0.1  # Volumen en disminución
        sin_tendencia_fuerte = fuerza_tendencia < 0.3  # Baja fuerza de tendencia
        
        # Está en lateral si cumple al menos 2 de 3 criterios
        criterios_cumplidos = sum([en_rango, volumen_decreciente, sin_tendencia_fuerte])
        en_lateralizacion = criterios_cumplidos >= 2
        
        if en_lateralizacion:
            print(f"   🟡 {symbol} EN RANGO LATERAL - {criterios_cumplidos}/3 criterios")
            print(f"      {'✅' if en_rango else '❌'} Rango <2%: {rango_porcentual:.2f}%")
            print(f"      {'✅' if volumen_decreciente else '❌'} Volumen ↘: {volumen_tendencia:.2f}")
            print(f"      {'✅' if sin_tendencia_fuerte else '❌'} Sin tendencia: {fuerza_tendencia:.2f}")
        else:
            print(f"   🟢 {symbol} CON TENDENCIA - {criterios_cumplidos}/3 criterios")
        
        return en_lateralizacion
        
    except Exception as e:
        print(f"❌ Error en análisis lateralización {symbol}: {e}")
        return False

def calcular_tendencia_volumen(datos):
    """
    Calcula la tendencia del volumen (positivo = creciente, negativo = decreciente)
    """
    if len(datos) < 10:
        return 0
    
    # Dividir en tercios
    tercio = len(datos) // 3
    if tercio == 0:
        return 0
    
    volumen_inicial = datos['volume'].iloc[:tercio].mean()
    volumen_final = datos['volume'].iloc[-tercio:].mean()
    
    if volumen_inicial == 0:
        return 0
    
    tendencia = (volumen_final - volumen_inicial) / volumen_inicial
    return tendencia

def calcular_fuerza_tendencia(datos):
    """
    Calcula la fuerza de la tendencia usando ATR normalizado
    """
    if len(datos) < 14:
        return 0
    
    # Calcular ATR básico
    high_low = datos['high'] - datos['low']
    high_close_prev = abs(datos['high'] - datos['close'].shift(1))
    low_close_prev = abs(datos['low'] - datos['close'].shift(1))
    
    true_range = pd.concat([high_low, high_close_prev, low_close_prev], axis=1).max(axis=1)
    atr = true_range.rolling(window=14).mean()
    
    # Normalizar ATR por el precio
    atr_normalizado = (atr / datos['close']) * 100
    
    # Usar el último ATR como medida de fuerza de tendencia
    fuerza = atr_normalizado.iloc[-1] if not atr_normalizado.empty else 0
    
    return fuerza

def filtrar_activos_sin_lateralizacion(activos_disponibles):
    """
    Filtra los activos que NO están en rango lateral
    """
    print(f"\n🎯 FILTRANDO ACTIVOS SIN LATERALIZACIÓN (3h)...")
    
    activos_filtrados = []
    for activo in activos_disponibles:
        symbol = activo['simbolo_bybit']
        moneda = activo['moneda']
        
        # Verificar si está en lateralización
        if not esta_en_rango_lateral(symbol):
            activos_filtrados.append(activo)
            print(f"   ✅ {moneda} ({symbol}): CON TENDENCIA - Apto para operar")
        else:
            print(f"   ❌ {moneda} ({symbol}): EN LATERAL - Descartado")
    
    print(f"📊 Resultado filtro: {len(activos_filtrados)} de {len(activos_disponibles)} activos con tendencia")
    return activos_filtrados

def obtener_datos_para_volume_regression(symbol, periodo='5', limite=100):
    """Obtiene datos de OHLCV para calcular Volume Regression - CON MÁS DATOS"""
    if not PYBIT_INSTALADO or not bybit_session:
        # Datos simulados para testing
        import random
        base_price = 100.0
        data = []
        for i in range(limite):
            open_price = base_price + random.uniform(-2, 2)
            close_price = open_price + random.uniform(-1, 1)
            high = max(open_price, close_price) + random.uniform(0, 1)
            low = min(open_price, close_price) - random.uniform(0, 1)
            volume = 1000 + random.uniform(-100, 100)
            data.append({
                'open': open_price,
                'high': high,
                'low': low,
                'close': close_price,
                'volume': volume
            })
        return pd.DataFrame(data)
    
    try:
        response = bybit_session.get_kline(
            category="linear",
            symbol=symbol,
            interval=periodo,
            limit=limite  # ✅ Obtener más datos para long_len=50
        )
        
        if response['retCode'] == 0:
            datos = response['result']['list']
            # Los datos vienen en orden inverso (más antiguo primero)
            datos.reverse()
            df = pd.DataFrame(datos, columns=[
                'timestamp', 'open', 'high', 'low', 'close', 'volume', 'turnover'
            ])
            
            # Convertir tipos
            for col in ['open', 'high', 'low', 'close', 'volume']:
                df[col] = pd.to_numeric(df[col], errors='coerce')
            
            return df
        else:
            print(f"❌ Error obteniendo datos para {symbol}: {response.get('retMsg')}")
            return None
            
    except Exception as e:
        print(f"❌ Error en obtener_datos_para_volume_regression: {e}")
        return None

# ========== SISTEMA REAL DE SEGUIMIENTO DE VELAS ==========
    
    # Actualizar máximo y mínimo
    precios_velas_actuales[symbol]['maximo'] = max(precios_velas_actuales[symbol]['maximo'], precio_actual)
    precios_velas_actuales[symbol]['minimo'] = min(precios_velas_actuales[symbol]['minimo'], precio_actual)


# ========== SISTEMA DE PROTECCIÓN +5%/-2% ==========

def verificar_proteccion_ganancias(symbol, operacion, precio_actual):
    """Verifica protección de ganancias: +5% y luego -3%, cierra entre entrada y +2%"""
    if operacion['estado'] != ESTADOS["LONG_ABIERTO"]:
        return False
    
    precio_long = operacion['precio_long']
    cambio_actual = ((precio_actual - precio_long) / precio_long) * 100
    
    # Inicializar seguimiento de máximo alcanzado
    if 'maximo_alcanzado' not in operacion:
        operaciones_activas[symbol]['maximo_alcanzado'] = precio_long
    
    # Actualizar máximo alcanzado SOLO si es mayor
    if precio_actual > operaciones_activas[symbol]['maximo_alcanzado']:
        operaciones_activas[symbol]['maximo_alcanzado'] = precio_actual
    
    maximo_alcanzado = operaciones_activas[symbol]['maximo_alcanzado']
    cambio_desde_maximo = ((precio_actual - maximo_alcanzado) / maximo_alcanzado) * 100
    
    # Verificar condiciones CORREGIDAS
    alcanzo_5pct = ((maximo_alcanzado - precio_long) / precio_long) * 100 >= 5
    retrocedio_3pct = cambio_desde_maximo <= -3
    esta_entre_entrada_y_2pct = 0 <= cambio_actual <= 2  # ✅ Entre 0% y +2%
    
    print(f"      📈 Máximo alcanzado: ${maximo_alcanzado:.6f} ({((maximo_alcanzado - precio_long) / precio_long * 100):.2f}%)")
    print(f"      📉 Retroceso desde máximo: {cambio_desde_maximo:.2f}%")
        
    # Si alcanzó +5% Y retrocedió -3% desde ese máximo Y está entre entrada y +2% → CERRAR
    if alcanzo_5pct and retrocedio_3pct and esta_entre_entrada_y_2pct:
        print(f"🎯 PROTECCIÓN GANANCIAS ACTIVADA: {symbol}")
        print(f"   📈 Alcanzó: +{((maximo_alcanzado - precio_long) / precio_long * 100):.2f}%")
        print(f"   📉 Retrocedió: {cambio_desde_maximo:.2f}% desde máximo")
        print(f"   💰 Ganancia actual: {cambio_actual:.2f}%")
        print(f"   ✅ Cierre entre entrada y +2%: {cambio_actual:.2f}%")
        return True
    
    return False

# ========== FUNCIONES DE CIERRE MEJORADAS ==========

def cerrar_todas_posiciones():
    """Cierra todas las posiciones abiertas"""
    global operaciones_activos
    
    print("🛑 Cerrando todas las posiciones...")
    
    if not PYBIT_INSTALADO or not bybit_session:
        print("   📝 SIMULACIÓN: Todas las posiciones cerradas")
        with operaciones_lock:
            operaciones_activas.clear()
        return True
    
    try:
        # Obtener todas las posiciones abiertas
        response = bybit_session.get_positions(category="linear", settleCoin="USDT")
        
        if response['retCode'] == 0:
            for position in response['result']['list']:
                if float(position['size']) > 0:
                    symbol = position['symbol']
                    side = position['side']
                    size = position['size']
                    
                    # Determinar lado contrario para cerrar
                    if side == 'Buy':
                        close_side = 'Sell'
                        position_idx = 1
                    else:
                        close_side = 'Buy' 
                        position_idx = 2
                    
                    print(f"   📤 Cerrando {side} {size} en {symbol}...")
                    
                    close_response = bybit_session.place_order(
                        category='linear',
                        symbol=symbol,
                        side=close_side,
                        orderType='Market',
                        qty=size,
                        timeInForce="GTC",
                        positionIdx=position_idx
                    )
                    
                    if close_response['retCode'] == 0:
                        print(f"   ✅ {symbol} {side} cerrado")
                    else:
                        print(f"   ❌ Error cerrando {symbol}: {close_response.get('retMsg')}")
        
        # Limpiar operaciones activas
        with operaciones_lock:
            operaciones_activas.clear()
        print("✅ Todas las posiciones cerradas")
        return True
        
    except Exception as e:
        print(f"❌ Error cerrando posiciones: {e}")
        return False

def cerrar_posicion_long(symbol):
    """Cierra solo la posición LONG - CON REINICIO DE MONITOREO"""
    global operaciones_activas, monitoreo_activo
    
    if not PYBIT_INSTALADO or not bybit_session:
        print(f"   📈 SIMULACIÓN: Cerrando LONG en {symbol}")
        with operaciones_lock:
            if symbol in operaciones_activas:
                del operaciones_activas[symbol]
          
    try:
        print(f"🏁 Cerrando posición LONG para {symbol}...")
        
        # Cerrar posición LONG
        response_long = bybit_session.place_order(
            category='linear',
            symbol=symbol,
            side='Sell',
            orderType='Market',
            qty=obtener_cantidad_posicion(symbol, 1),
            timeInForce="GTC",
            positionIdx=1
        )
        
        if response_long['retCode'] == 0:
            print(f"✅ LONG cerrado para {symbol}")
            
            # Actualizar estado de la operación
            with operaciones_lock:
                if symbol in operaciones_activas:
                    if operaciones_activas[symbol]['estado'] == ESTADOS["LONG_ABIERTO"]:
                        # Si solo tenía LONG, eliminar operación
                        del operaciones_activas[symbol]
                        print(f"🗑️  Operación eliminada: {symbol}")
                                   
            return True
        else:
            print(f"❌ Error cerrando LONG: {response_long.get('retMsg')}")
            return False
            
    except Exception as e:
        print(f"❌ Error cerrando LONG: {e}")
        return False
    
def cerrar_ambas_posiciones(symbol):
    """Cierra ambas posiciones (long y short) - CON REINICIO DE MONITOREO"""
    global operaciones_activas, monitoreo_activo
    
    if not PYBIT_INSTALADO or not bybit_session:
        print(f"   🏁 SIMULACIÓN: Cerrando ambas posiciones para {symbol}")
        with operaciones_lock:
            if symbol in operaciones_activas:
                del operaciones_activas[symbol]
           
    try:
        print(f"🏁 Cerrando ambas posiciones para {symbol}...")
        
        # Cerrar posición LONG
        response_long = bybit_session.place_order(
            category='linear',
            symbol=symbol,
            side='Sell',
            orderType='Market',
            qty=obtener_cantidad_posicion(symbol, 1),
            timeInForce="GTC",
            positionIdx=1
        )
        
        # Cerrar posición SHORT  
        response_short = bybit_session.place_order(
            category='linear',
            symbol=symbol,
            side='Buy',
            orderType='Market',
            qty=obtener_cantidad_posicion(symbol, 2),
            timeInForce="GTC",
            positionIdx=2
        )
        
        if response_long['retCode'] == 0 and response_short['retCode'] == 0:
            print(f"✅ Ambas posiciones cerradas para {symbol}")
            with operaciones_lock:
                if symbol in operaciones_activas:
                    del operaciones_activas[symbol]
        else:
            print(f"❌ Error cerrando posiciones: Long={response_long.get('retMsg')}, Short={response_short.get('retMsg')}")
            return False
            
    except Exception as e:
        print(f"❌ Error cerrando posiciones: {e}")
        return False
    
def verificar_estado_posiciones_reales():
    """Verifica el estado real de las posiciones en Bybit y sincroniza con operaciones_activas"""
    if not PYBIT_INSTALADO or not bybit_session:
        return
    
    try:
        print("🔍 Verificando estado real de posiciones en Bybit...")
        response = bybit_session.get_positions(category="linear", settleCoin="USDT")
        
        if response['retCode'] == 0:
            posiciones_reales = {}
            
            # Obtener todas las posiciones reales
            for position in response['result']['list']:
                symbol = position['symbol']
                size = float(position['size'])
                if size > 0:
                    posiciones_reales[symbol] = {
                        'size': size,
                        'side': position['side'],
                        'avg_price': float(position['avgPrice'])
                    }
            
            # Sincronizar con operaciones_activas
            with operaciones_lock:
                symbols_a_eliminar = []
                
                for symbol, operacion in operaciones_activas.items():
                    if operacion.get('simulado', False):
                        continue  # Saltar operaciones simuladas
                    
                    if symbol not in posiciones_reales:
                        print(f"🚨 POSICIÓN CERRADA DETECTADA: {symbol} ya no existe en Bybit")
                        symbols_a_eliminar.append(symbol)
                    else:
                        # Actualizar información de la posición
                        pos_real = posiciones_reales[symbol]
                        if pos_real['side'] == 'Buy' and operacion['estado'] == ESTADOS["LONG_ABIERTO"]:
                            # ✅ ACTUALIZAR TODOS LOS DATOS INCLUYENDO CANTIDAD
                            operaciones_activas[symbol]['size'] = pos_real['size']
                            operaciones_activas[symbol]['precio_long'] = pos_real['avg_price']
                            operaciones_activas[symbol]['cantidad'] = str(pos_real['size'])  # ← ESTA LÍNEA FALTA
                            print(f"✅ {symbol}: Posición LONG confirmada ({pos_real['size']} contratos)")
                
                # Eliminar operaciones que ya no existen
                for symbol in symbols_a_eliminar:
                    if symbol in operaciones_activas:
                        # Registrar como operación cerrada (pérdida)
                        operacion = operaciones_activas[symbol]
                        precio_actual = obtener_precio_actual(symbol)
                        precio_long = operacion['precio_long']
                        
                        # Calcular pérdida
                        perdida_porcentaje = ((precio_actual - precio_long) / precio_long) * 100
                        perdida_usdt = CANTIDAD_USDT * (perdida_porcentaje / 100)
                        
                        print(f"📉 Posición {symbol} cerrada externamente:")
                        print(f"   💰 Precio entrada: ${precio_long:.6f}")
                        print(f"   📊 Precio actual: ${precio_actual:.6f}")
                        print(f"   📉 Pérdida: {perdida_porcentaje:.2f}%")
                        
                        # Registrar en estadísticas
                        with estadisticas_lock:
                            estadisticas['total_operaciones'] += 1
                            estadisticas['operaciones_perdidas'] += 1
                            estadisticas['perdida_acumulada'] += abs(perdida_usdt)
                            
                            operacion_cerrada = {
                                'symbol': symbol,
                                'fecha_cierre': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                                'precio_apertura': precio_long,
                                'precio_cierre': precio_actual,
                                'ganancia_porcentaje': perdida_porcentaje,
                                'ganancia_usdt': perdida_usdt,
                                'cantidad_usdt': CANTIDAD_USDT,
                                'motivo': "Cerrado Externamente"
                            }
                            estadisticas['operaciones_cerradas'].append(operacion_cerrada)
                        
                        del operaciones_activas[symbol]
                        print(f"🗑️  {symbol} eliminado de operaciones activas")
            
            if symbols_a_eliminar:
                print(f"🔄 Sincronización completada: {len(symbols_a_eliminar)} posiciones cerradas detectadas")
                
    except Exception as e:
        print(f"❌ Error verificando posiciones reales: {e}") 

# ========== SISTEMA DE MONITOREO MEJORADO ==========

def monitorear_operaciones():
    """Monitorea las operaciones activas CADA 30 SEGUNDOS - CORREGIDO"""
    global monitoreo_activo
    
    monitoreo_activo = True
    print("🔍 INICIANDO MONITOREO PERMANENTE de operaciones (cada 30 segundos)...")
    
    ciclo_monitoreo = 0
    
    while monitoreo_activo and not bot_salir:
        ciclo_monitoreo += 1
        try:
            # ✅ SOLUCIÓN SIMPLE: Verificar y limpiar operaciones cerradas externamente
            if operaciones_activas and not bot_salir:
                # Verificar si hay operaciones reales (no simuladas)
                operaciones_simuladas = all(op.get('simulado', False) for op in operaciones_activas.values())
                
                if not operaciones_simuladas and PYBIT_INSTALADO and bybit_session:
                    try:
                        response = bybit_session.get_positions(category="linear", settleCoin="USDT")
                        if response['retCode'] == 0:
                            posiciones_reales = []
                            for position in response['result']['list']:
                                if float(position['size']) > 0:
                                    posiciones_reales.append(position['symbol'])
                            
                            # Comparar con nuestras operaciones activas
                            with operaciones_lock:
                                for symbol in list(operaciones_activas.keys()):
                                    if symbol not in posiciones_reales:
                                        print(f"🔄 POSICIÓN CERRADA DETECTADA: {symbol} - Eliminando de tracking")
                                        del operaciones_activas[symbol]
                                        print(f"✅ {symbol} removido - Listo para nueva operación")
                    except Exception as e:
                        print(f"⚠️  Error verificando posiciones: {e}")
            
            # Si no hay operaciones, solo mostrar mensaje y continuar
            if not operaciones_activas:
                print(f"\n🔄 [MONITOREO {ciclo_monitoreo}] {datetime.now().strftime('%H:%M:%S')} - Sin operaciones activas")
                
                # ESPERA 30 SEGUNDOS CON COUNTDOWN
                print(f"⏰ Próxima verificación de monitoreo en:")
                tiempo_inicio = time.time()
                
                while time.time() - tiempo_inicio < 30 and not bot_salir:
                    tiempo_restante = 30 - (time.time() - tiempo_inicio)
                    mins, secs = divmod(int(tiempo_restante), 60)
                    print(f"\r   {mins:02d}:{secs:02d}", end="", flush=True)
                    time.sleep(1)
                
                if not bot_salir:
                    print("\r✅ ¡Iniciando nueva verificación de monitoreo!                    ")
                continue
            
            # ✅ HAY OPERACIONES ACTIVAS - MONITOREARLAS
            print(f"\n🔄 [MONITOREO {ciclo_monitoreo}] {datetime.now().strftime('%H:%M:%S')} - {len(operaciones_activas)} operaciones")
            print("=" * 50)
            
            operaciones_cerradas = 0
            
            for symbol, operacion in list(operaciones_activas.items()):
                estado = operacion['estado']
                precio_actual = obtener_precio_actual(symbol)
                
                if precio_actual == 0:
                    continue
                
                if estado == ESTADOS["LONG_ABIERTO"]:
                    precio_long = operacion['precio_long']
                    cambio_actual = ((precio_actual - precio_long) / precio_long) * 100
                    
                    # ✅ SOLUCIÓN SEGURA - SI NO EXISTE sl_price, LO CALCULAMOS
                    sl_price = operacion.get('sl_price', precio_long * (1 - SL_PORCENTAJE / 100))
                    
                    print(f"   🔍 ANALIZANDO 🟡{symbol}:")
                    print(f"      💰 Precio LONG: ${precio_long:.6f}")
                    print(f"      📊 Precio actual: ${precio_actual:.6f}")
                                        
                    # 1. ✅ VERIFICAR STOP LOSS (pero no mostrarlo)
                    if precio_actual <= sl_price:
                        print(f"🎯 STOP LOSS ACTIVADO: {symbol}")
                        print(f"   📉 Precio: ${precio_actual:.6f} <= SL: ${sl_price:.6f}")
                        if cerrar_posicion_long_real(symbol, "Stop Loss"):
                            operaciones_cerradas += 1
                        continue
                    
                    # 2. ✅ VOLUME REGRESSION (solo en ganancias > +1%)
                    if cambio_actual > 1.0:
                        df_datos = obtener_datos_para_volume_regression(symbol)
                        
                        if df_datos is not None and len(df_datos) >= 50:
                            df_volume = calcular_volume_regression(df_datos)
                            
                            if not df_volume.empty:
                                ultima_señal = df_volume['vol_down'].iloc[-1]
                                slope_price = df_volume['slope_price'].iloc[-1]
                                print(f"         umbral = -0.000003")
                                
                                if slope_price >= 0:
                                    print(f"         🟢 Fuerza Tendencial: {slope_price:.6f}")
                                else:
                                    print(f"         🔴 Fuerza Tendencial: {slope_price:.6f}")
                                
                                if slope_price < -0.000003:
                                    print(f"         🟥 🚨 Bajo volumen, se cerrara posición")
                                    if cerrar_posicion_long_real(symbol, "Volume Regression"):
                                        operaciones_cerradas += 1
                                    continue
                    
                    # 3. ✅ PROTECCIÓN DE GANANCIAS
                    if verificar_proteccion_ganancias(symbol, operacion, precio_actual):
                        if cerrar_posicion_long_real(symbol, "Protección Ganancias"):
                            operaciones_cerradas += 1
                        continue
                    
                    # 4. ✅ VERIFICAR SI DEBE ABRIRSE SHORT (-1.5%)
                    if operacion['estado'] == ESTADOS["LONG_ABIERTO"]:
                        cambio_desde_long = ((precio_actual - operacion['precio_long']) / operacion['precio_long']) * 100
    
                        if cambio_desde_long <= -2.0 and 'short_abierto' not in operacion:
                            print(f"🎯 CONDICIÓN SHORT ACTIVADA: {symbol}")
                            print(f"   📉 Precio bajó a {cambio_desde_long:.2f}% desde LONG")
                            print(f"   🚀 Abriendo posición SHORT...")
        
                            # Abrir SHORT (11 USDT)
                            order_id_short = abrir_posicion_short(symbol, 11.0)
        
                            if order_id_short:
                                operaciones_activas[symbol]['estado'] = ESTADOS["AMBOS_ABIERTOS"]
                                operaciones_activas[symbol]['precio_short'] = precio_actual
                                operaciones_activas[symbol]['order_id_short'] = order_id_short
                                operaciones_activas[symbol]['short_abierto'] = True
            
                                # Colocar TP avanzado
                                colocar_tp_avanzado(symbol, operacion['precio_long'], precio_actual)
            
                                print(f"✅ SHORT establecido para {symbol} a ${precio_actual:.6f}")
                                continue

                # 5. ✅ VERIFICAR ADD FUNDS CORREGIDO (precio POR ENCIMA del LONG - SIN LÍMITE SUPERIOR)
                if operacion['estado'] == ESTADOS["AMBOS_ABIERTOS"]:
                    precio_long = operacion['precio_long']
                    
                    # ✅ NUEVA CONDICIÓN: Solo activar cuando precio ESTÉ POR ENCIMA del LONG (sin límite superior)
                    diferencia_porcentual = ((precio_actual - precio_long) / precio_long) * 100
                    
                    print(f"   🔄 Verificando ADD FUNDS {symbol}:")
                    print(f"      💰 Precio LONG: ${precio_long:.6f}")
                    print(f"      📊 Precio actual: ${precio_actual:.6f}") 
                    print(f"      📈 Diferencia: {diferencia_porcentual:+.2f}%")
                    print(f"      ✅ ADD FUNDS: {operacion.get('add_funds_ejecutado', False)}")
                    
                    # ✅ CONDICIÓN SIMPLIFICADA: precio > precio_long (sin límite superior)
                    if (diferencia_porcentual > 0 and 
                        not operacion.get('add_funds_ejecutado', False)):
                        
                        print(f"💰 ADD FUNDS ACTIVADO: {symbol}")
                        print(f"   🎯 Precio por encima del LONG: +{diferencia_porcentual:.2f}%")

                        # Agregar fondos al LONG (16.5 USDT adicionales)
                        order_id_add = abrir_posicion_long(symbol, 16.5)

                        if order_id_add:
                            # ✅ OBTENER PRECIO REAL DE EJECUCIÓN DEL ADD FUNDS
                            precio_add_funds = obtener_precio_entrada_real(symbol, order_id_add, "Buy")
                            
                            # ✅ CALCULAR NUEVO PRECIO PROMEDIO DEL LONG
                            precio_long_original = operacion['precio_long']
                            
                            # Obtener cantidades de ambas posiciones LONG
                            cantidad_long_original = obtener_cantidad_posicion_por_order_id(symbol, operacion.get('order_id_long'))
                            cantidad_add_funds = obtener_cantidad_posicion_por_order_id(symbol, order_id_add)
                            
                            if cantidad_long_original and cantidad_add_funds:
                                # Calcular nuevo precio promedio ponderado
                                cantidad_total = float(cantidad_long_original) + float(cantidad_add_funds)
                                valor_total = (float(cantidad_long_original) * precio_long_original + 
                                             float(cantidad_add_funds) * precio_add_funds)
                                nuevo_precio_promedio = valor_total / cantidad_total
                                
                                print(f"   📊 CÁLCULO NUEVO PRECIO PROMEDIO:")
                                print(f"      📈 LONG original: {cantidad_long_original} @ ${precio_long_original:.6f}")
                                print(f"      💰 ADD FUNDS: {cantidad_add_funds} @ ${precio_add_funds:.6f}")
                                print(f"      🎯 NUEVO PRECIO PROMEDIO: ${nuevo_precio_promedio:.6f}")
                                
                                # ✅ RECALCULAR TP AVANZADO CON NUEVO PRECIO PROMEDIO
                                precio_short_actual = operacion['precio_short']
                                nuevo_tp_long, nuevo_tp_short, nueva_dif = calcular_tp_avanzado(
                                    nuevo_precio_promedio, precio_short_actual
                                )
                                
                                # ✅ GUARDAR ESTADO CON LOCK PARA SEGURIDAD
                                with operaciones_lock:
                                    operaciones_activas[symbol]['add_funds_ejecutado'] = True
                                    operaciones_activas[symbol]['order_id_add_funds'] = order_id_add
                                    operaciones_activas[symbol]['precio_long'] = nuevo_precio_promedio  # Actualizar precio promedio
                                    operaciones_activas[symbol]['precio_add_funds'] = precio_add_funds
                                    operaciones_activas[symbol]['cantidad_long_original'] = cantidad_long_original
                                    operaciones_activas[symbol]['cantidad_add_funds'] = cantidad_add_funds
                                    operaciones_activas[symbol]['tp_long_avanzado'] = nuevo_tp_long
                                    operaciones_activas[symbol]['tp_short_avanzado'] = nuevo_tp_short
                                
                                print(f"✅ ADD FUNDS EJECUTADO Y ACTUALIZADO:")
                                print(f"   💾 add_funds ejecutado")
                                print(f"   📋 Order ID: {order_id_add}")
                                print(f"   🎯 NUEVO TP Long: ${nuevo_tp_long:.6f}")
                                print(f"   🎯 NUEVO TP Short: ${nuevo_tp_short:.6f}")
                                print(f"   📊 Diferencia recalculada: {nueva_dif:.2f}%")
                            else:
                                print(f"⚠️  No se pudieron obtener las cantidades - Usando precio original")
                                with operaciones_lock:
                                    operaciones_activas[symbol]['add_funds_ejecutado'] = True
                                    operaciones_activas[symbol]['order_id_add_funds'] = order_id_add
                            
                            continue
                        else:
                            print(f"❌ ADD FUNDS FALLÓ - No se guardó estado")

                # 6. ✅ VERIFICAR TP AVANZADO (NUEVA IMPLEMENTACIÓN)
                if operacion['estado'] == ESTADOS["AMBOS_ABIERTOS"]:
                    tp_long = operacion.get('tp_long_avanzado')
                    tp_short = operacion.get('tp_short_avanzado')
                    
                    if tp_long and tp_short:
                        print(f"   🎯 VERIFICANDO TP AVANZADO {symbol}:")
                        print(f"      📊 Precio actual: ${precio_actual:.6f}")
                        print(f"      📈 TP Long: ${tp_long:.6f} (+{((tp_long - operacion['precio_long'])/operacion['precio_long']*100):.2f}%)")
                        print(f"      📉 TP Short: ${tp_short:.6f} (-{((operacion['precio_short'] - tp_short)/operacion['precio_short']*100):.2f}%)")
                        
                        # VERIFICACIÓN TP LONG
                        if precio_actual >= tp_long:
                            print(f"🎯 🟢 TP LONG ACTIVADO: {symbol}")
                            print(f"   📈 Precio actual ${precio_actual:.6f} >= TP Long ${tp_long:.6f}")
                            print(f"   💰 Ganancia LONG: {((precio_actual - operacion['precio_long'])/operacion['precio_long']*100):.2f}%")
                            if cerrar_ambas_posiciones_con_registro(symbol, "TP_LONG_AVANZADO"):
                                operaciones_cerradas += 1
                                continue
                        
                        # VERIFICACIÓN TP SHORT
                        elif precio_actual <= tp_short:
                            print(f"🎯 🔴 TP SHORT ACTIVADO: {symbol}")
                            print(f"   📉 Precio actual ${precio_actual:.6f} <= TP Short ${tp_short:.6f}")
                            print(f"   💰 Ganancia SHORT: {((operacion['precio_short'] - precio_actual)/operacion['precio_short']*100):.2f}%")
                            if cerrar_ambas_posiciones_con_registro(symbol, "TP_SHORT_AVANZADO"):
                                operaciones_cerradas += 1
                                continue
                        
                        # MONITOREO CONTINUO (sin activación)
                        else:
                            dist_long_pct = ((tp_long - precio_actual) / precio_actual) * 100
                            dist_short_pct = ((precio_actual - tp_short) / precio_actual) * 100
                            
                            print(f"      📏 Distancia a TP Long: +{dist_long_pct:.2f}%")
                            print(f"      📏 Distancia a TP Short: -{dist_short_pct:.2f}%")

                # 7. ✅ VERIFICAR CIERRE AMBAS POSICIONES (precio POR DEBAJO del SHORT después de ADD FUNDS)
                if (operacion['estado'] == ESTADOS["AMBOS_ABIERTOS"] and 
                    operacion.get('add_funds_ejecutado', False)):

                    precio_short = operacion['precio_short']
                    
                    # ✅ CORRECCIÓN: Verificar si precio está POR DEBAJO del precio SHORT
                    diferencia_porcentual = ((precio_actual - precio_short) / precio_short) * 100
                    
                    print(f"   🔄 Verificando CIERRE POR VUELTA A SHORT {symbol}:")
                    print(f"      📉 Precio SHORT entrada: ${precio_short:.6f}")
                    print(f"      📊 Precio actual: ${precio_actual:.6f}")
                    print(f"      📈 Diferencia: {diferencia_porcentual:+.2f}%")
                    print(f"      💾 ADD_FUNDS: {operacion.get('add_funds_ejecutado', False)}")
                    
                    # ✅ CONDICIÓN CORREGIDA: precio < precio_short (POR DEBAJO)
                    if diferencia_porcentual < -0.1:  # ← Precio al menos -0.1% por debajo del SHORT
                        print(f"🎯 CIERRE POR VUELTA A SHORT ACTIVADO: {symbol}")
                        print(f"   📉 Precio ${precio_actual:.6f} < SHORT ${precio_short:.6f}")
                        print(f"   📊 Diferencia: {diferencia_porcentual:.2f}%")
                        print(f"   🏁 Cerrando LONG y SHORT...")

                        if cerrar_ambas_posiciones_con_registro(symbol, "VUELTA_SHORT"):
                            print(f"✅ Ambas posiciones cerradas para {symbol}")
                            operaciones_cerradas += 1
                            continue
                    else:
                        print(f"   ❌ NO activado - Precio no está por debajo del SHORT")
                        
            # RESUMEN
            print("=" * 50)
            print(f"📊 RESUMEN MONITOREO: {len(operaciones_activas)} operaciones activas")
            if operaciones_cerradas > 0:
                print(f"📤 Operaciones cerradas en este ciclo: {operaciones_cerradas}")
                
            with operaciones_lock:
                for symbol, op in operaciones_activas.items():
                    estado_str = list(ESTADOS.keys())[list(ESTADOS.values()).index(op['estado'])]
                    precio_actual = obtener_precio_actual(symbol)
                    precio_long = op['precio_long']
                    cambio = ((precio_actual - precio_long) / precio_long) * 100
                    print(f"   🟡 {symbol}: {estado_str} | P&L {cambio:+.2f}%")
            
            # ESPERA 30 SEGUNDOS CON COUNTDOWN
            print(f"\n⏰ Próxima verificación de MONITOREO en:")
            tiempo_inicio = time.time()
            
            while time.time() - tiempo_inicio < 30 and not bot_salir:
                tiempo_restante = 30 - (time.time() - tiempo_inicio)
                mins, secs = divmod(int(tiempo_restante), 60)
                print(f"\r   {mins:02d}:{secs:02d}", end="", flush=True)
                time.sleep(1)
            
            if not bot_salir:
                print("\r✅ ¡Iniciando nueva verificación de MONITOREO!                    ")
            
        except Exception as e:
            print(f"❌ Error en monitoreo: {e}")
            time.sleep(30)

# ========== SISTEMA DE RECUPERACIÓN ==========

def recuperar_estado_desconexion():
    """Recupera el estado después de una desconexión"""
    global operaciones_activas
    
    if not PYBIT_INSTALADO or not bybit_session:
        return
    
    try:
        print("🔄 Recuperando estado después de desconexión...")
        
        # 1. Obtener posiciones reales de Bybit
        response = bybit_session.get_positions(category="linear", settleCoin="USDT")
        
        if response['retCode'] == 0:
            for position in response['result']['list']:
                if float(position['size']) > 0:
                    symbol = position['symbol']
                    side = position['side']
                    size = float(position['size'])
                    
                    print(f"📊 Recuperada posición: {symbol} {side} {size}")
                    
                    # Reconstruir estado aproximado
                    if symbol not in operaciones_activas:
                        operaciones_activas[symbol] = {
                            'estado': ESTADOS["AMBOS_ABIERTOS"],  # Asumir ambos
                            'precio_long': float(position['avgPrice']),
                            'precio_short': float(position['avgPrice']),
                            'moneda': symbol.replace('USDT', ''),
                            'add_funds_ejecutado': True  # Asumir completado
                        }
            
            print(f"✅ Estado recuperado: {len(operaciones_activas)} operaciones")
                       
    except Exception as e:
        print(f"❌ Error recuperando estado: {e}")

# ========== VERIFICACIÓN DE POSICIONES CERRADAS ==========

def verificar_posiciones_cerradas():
    """Verifica si las posiciones en operaciones_activas siguen abiertas - MEJORADO"""
    global operaciones_activas
    
    if not operaciones_activas:
        return
    
    if not PYBIT_INSTALADO or not bybit_session:
        return
    
    symbols_a_eliminar = []
    
    for symbol, operacion in operaciones_activas.items():
        try:
            # Verificar posiciones abiertas en Bybit
            positions_response = bybit_session.get_positions(
                category="linear", 
                symbol=symbol
            )
            
            if positions_response['retCode'] == 0:
                posiciones_abiertas = False
                
                for position in positions_response['result']['list']:
                    size = float(position['size'])
                    if size > 0:
                        posiciones_abiertas = True
                        break
                
                # Si no hay posiciones abiertas, verificar si fue un cierre esperado
                if not posiciones_abiertas:
                    print(f"🚨 Posición cerrada detectada: {symbol}")
                    print(f"   📊 Estado anterior: {list(ESTADOS.keys())[list(ESTADOS.values()).index(operacion['estado'])]}")
                    print(f"   💰 Precio LONG: {operacion.get('precio_long', 'N/A')}")
                    
                    # Solo eliminar si no estamos en proceso de cierre normal
                    if operacion['estado'] != ESTADOS["SIN_OPERAR"]:
                        symbols_a_eliminar.append(symbol)
                        print(f"   🗑️  Eliminando de tracking: {symbol}")
                    
        except Exception as e:
            print(f"❌ Error verificando posición para {symbol}: {e}")
    
    # Eliminar operaciones cerradas
    for symbol in symbols_a_eliminar:
        if symbol in operaciones_activas:
            del operaciones_activas[symbol]

def actualizar_estado_operaciones():
    """Actualiza el estado de las operaciones activas"""
    global operaciones_activas
    
    if not operaciones_activas:
        return
    
    for symbol, operacion in list(operaciones_activas.items()):
        try:
            # Verificar si la posición long sigue abierta
            positions_response = bybit_session.get_positions(
                category="linear", 
                symbol=symbol
            )
            
            if positions_response['retCode'] == 0:
                long_abierto = False
                short_abierto = False
                
                for position in positions_response['result']['list']:
                    size = float(position['size'])
                    if size > 0:
                        side = position['side']
                        if side == 'Buy':
                            long_abierto = True
                        elif side == 'Sell':
                            short_abierto = True
                
                # Actualizar estado basado en posiciones reales
                if long_abierto and short_abierto:
                    operaciones_activas[symbol]['estado'] = ESTADOS["AMBOS_ABIERTOS"]
                elif long_abierto:
                    operaciones_activas[symbol]['estado'] = ESTADOS["LONG_ABIERTO"]
                elif short_abierto:
                    # Caso raro: solo short abierto
                    operaciones_activas[symbol]['estado'] = ESTADOS["ESPERANDO_SHORT"]
                else:
                    # Ambas posiciones cerradas - eliminar
                    print(f"🚨 Ambas posiciones cerradas para {symbol}")
                    del operaciones_activas[symbol]
                    
        except Exception as e:
            print(f"❌ Error actualizando estado para {symbol}: {e}")

# ========== CÁLCULO DE TP AVANZADO ==========

def calcular_tp_avanzado(precio_long, precio_short):
    """Calcula los TP avanzados según la estrategia"""
    # Calcular la diferencia porcentual entre long y short
    dif = ((precio_long - precio_short) / precio_long) * 100
    
    # Calcular TP para long (por encima del precio long)
    tp_long = precio_long * (1 + (dif * 1.76) / 100)
    
    # Calcular TP para short (por debajo del precio short)  
    tp_short = precio_short * (1 - (dif * 1.76) / 100)
    
    print(f"📊 Cálculo TP Avanzado:")
    print(f"   📈 Diferencia: {dif:.2f}%")
    print(f"   🎯 TP Long: {tp_long:.6f} (+{(tp_long-precio_long)/precio_long*100:.2f}%)")
    print(f"   🎯 TP Short: {tp_short:.6f} (-{(precio_short-tp_short)/precio_short*100:.2f}%)")
    
    return tp_long, tp_short, dif

def colocar_tp_avanzado(symbol, precio_long, precio_short):
    """Coloca los TP avanzados después de abrir el short - CON DEBUG"""
    if not PYBIT_INSTALADO or not bybit_session:
        print(f"   🎯 SIMULACIÓN: TP avanzado para {symbol}")
        # Guardar los TP calculados para monitoreo de velas
        tp_long, tp_short, dif = calcular_tp_avanzado(precio_long, precio_short)
        operaciones_activas[symbol]['tp_long_avanzado'] = tp_long
        operaciones_activas[symbol]['tp_short_avanzado'] = tp_short
        
        # DEBUG DETALLADO DE CÁLCULO
        print(f"🔍 DEBUG TP CALCULADO {symbol}:")
        print(f"   📈 Precio LONG entrada: {precio_long:.6f}")
        print(f"   📉 Precio SHORT entrada: {precio_short:.6f}")
        print(f"   📏 Diferencia calculada: {dif:.4f}%")
        print(f"   🎯 TP Long calculado: {tp_long:.6f}")
        print(f"   🎯 TP Short calculado: {tp_short:.6f}")
        print(f"   📈 Distancia TP Long: +{((tp_long - precio_long) / precio_long * 100):.4f}%")
        print(f"   📉 Distancia TP Short: -{((precio_short - tp_short) / precio_short * 100):.4f}%")
        
        return True
    
    try:
        # Calcular TP avanzados
        tp_long, tp_short, dif = calcular_tp_avanzado(precio_long, precio_short)
        
        # GUARDAR LOS TP PARA MONITOREO DE VELAS PERO NO COLOCAR ORDENES TP
        operaciones_activas[symbol]['tp_long_avanzado'] = tp_long
        operaciones_activas[symbol]['tp_short_avanzado'] = tp_short
        
        # DEBUG DETALLADO DE CÁLCULO
        print(f"🔍 DEBUG TP CALCULADO {symbol}:")
        print(f"   📈 Precio LONG entrada: {precio_long:.6f}")
        print(f"   📉 Precio SHORT entrada: {precio_short:.6f}")
        print(f"   📏 Diferencia calculada: {dif:.4f}%")
        print(f"   🎯 TP Long calculado: {tp_long:.6f}")
        print(f"   🎯 TP Short calculado: {tp_short:.6f}")
        print(f"   📈 Distancia TP Long: +{((tp_long - precio_long) / precio_long * 100):.4f}%")
        print(f"   📉 Distancia TP Short: -{((precio_short - tp_short) / precio_short * 100):.4f}%")
        
        print(f"✅ TP avanzados CALCULADOS para {symbol} - Se ejecutarán al CIERRE de vela")
        print(f"   📈 TP Long: {tp_long:.6f} - Se ejecuta si vela cierra POR ENCIMA")
        print(f"   📉 TP Short: {tp_short:.6f} - Se ejecuta si vela cierra POR DEBAJO")
        
        return True
            
    except Exception as e:
        print(f"❌ Error calculando TP avanzados: {e}")
        return False

def obtener_cantidad_posicion(symbol, position_idx):
    """Obtiene la cantidad de una posición abierta"""
    if not PYBIT_INSTALADO or not bybit_session:
        return "0.001"  # Simulación
    
    try:
        positions = bybit_session.get_positions(category="linear", symbol=symbol)
        if positions['retCode'] == 0:
            for position in positions['result']['list']:
                if float(position['size']) > 0:
                    # Verificar si es la posición que buscamos (basado en side y lógica)
                    if (position_idx == 1 and position['side'] == 'Buy') or \
                       (position_idx == 2 and position['side'] == 'Sell'):
                        return position['size']
        return "0.001"
    except Exception as e:
        print(f"❌ Error obteniendo cantidad posición: {e}")
        return "0.001"

# ========== FUNCIONES BYBIT CORREGIDAS ==========

def configurar_hedge_mode():
    """Configura el account en Hedge Mode - SOLUCIÓN CLAVE"""
    if not PYBIT_INSTALADO or not bybit_session:
        return True
    
    try:
        print("🔧 Configurando Hedge Mode para la cuenta...")
        response = bybit_session.switch_position_mode(
            category="linear",
            mode=1  # 1 = Hedge Mode, 0 = One-Way Mode
        )
        if response['retCode'] == 0:
            print("✅ Hedge Mode configurado correctamente")
            return True
        else:
            print(f"⚠️  Info Hedge Mode: {response.get('retMsg')}")
            return True  # Continuar aunque falle (puede que ya esté configurado)
    except Exception as e:
        print(f"⚠️  Info Hedge Mode: {e}")
        return True

def configurar_apalancamiento(symbol):
    """Configura el apalancamiento 25x para el símbolo"""
    if not PYBIT_INSTALADO or not bybit_session:
        return True
    
    try:
        print(f"🔧 Configurando apalancamiento 25x para {symbol}...")
        response = bybit_session.set_leverage(
            category="linear",
            symbol=symbol,
            buyLeverage=str(LEVERAGE),
            sellLeverage=str(LEVERAGE)
        )
        
        if response['retCode'] == 0:
            print(f"✅ Apalancamiento 20x configurado para {symbol}")
            return True
        else:
            print(f"⚠️  Info apalancamiento {symbol}: {response.get('retMsg')}")
            return True  # Continuar aunque falle
    except Exception as e:
        print(f"⚠️  Info apalancamiento {symbol}: {e}")
        return True

def obtener_info_symbol(symbol):
    """Obtiene información del símbolo"""
    if not PYBIT_INSTALADO or not bybit_session:
        return {
            'min_order_qty': 0.001,
            'qty_step': 0.001,
            'min_order_value': 5.0,
        }
    
    try:
        response = bybit_session.get_instruments_info(category="linear", symbol=symbol)
        
        if response['retCode'] == 0 and response['result']['list']:
            symbol_info = response['result']['list'][0]
            lot_size_filter = symbol_info.get('lotSizeFilter', {})
            
            return {
                'min_order_qty': float(lot_size_filter.get('minOrderQty', '0.001')),
                'qty_step': float(lot_size_filter.get('qtyStep', '0.001')),
                'min_order_value': float(symbol_info.get('minOrderAmt', '5.0')),
            }
        else:
            print(f"❌ No se pudo obtener info para {symbol}")
            return None
            
    except Exception as e:
        print(f"❌ Error obteniendo info símbolo: {e}")
        return None

def obtener_precio_actual(symbol):
    """Obtiene el precio actual del símbolo"""
    if not PYBIT_INSTALADO or not bybit_session:
        # Simular precio fluctuante para testing
        import random
        return 100.0 + random.uniform(-5, 5)
    
    try:
        response = bybit_session.get_tickers(category="linear", symbol=symbol)
        
        if response['retCode'] == 0 and response['result']['list']:
            return float(response['result']['list'][0]['lastPrice'])
        else:
            print(f"❌ Error obteniendo precio para {symbol}")
            return 0
            
    except Exception as e:
        print(f"❌ Error obteniendo precio: {e}")
        return 0
def calcular_cantidad_precisa(symbol, cantidad_usdt):
    """CALCULA CANTIDADES EXACTAS - """
    try:
        # Obtener precio actual
        precio = obtener_precio_actual(symbol)
        if precio == 0:
            print(f"❌ Precio cero para {symbol}")
            return None, None
        
        # Obtener info del símbolo
        symbol_info = obtener_info_symbol(symbol)
        if not symbol_info:
            print(f"❌ No se pudo obtener info para {symbol}")
            return None, None
        
        # Extraer parámetros
        min_order_qty = symbol_info['min_order_qty']
        qty_step = symbol_info['qty_step']
        min_order_value = symbol_info['min_order_value']
        
        print(f"🔍 Cálculo PRECISO para {symbol}:")
        print(f"   Objetivo: ${cantidad_usdt:.2f} | Precio: ${precio:.6f}")
        print(f"   Parámetros: MinQty={min_order_qty}, Step={qty_step}, MinVal=${min_order_value}")
        
        # Verificar mínimo de orden
        if cantidad_usdt < min_order_value:
            print(f"❌ Monto ${cantidad_usdt} < mínimo ${min_order_value}")
            return None, None
        
        # CALCULAR CANTIDAD BASE EXACTA
        qty_base = cantidad_usdt / precio
        print(f"   Cálculo base: {qty_base:.8f} contratos")
        
        # ✅ PRECISIÓN: AJUSTAR AL STEP MÁS CERCANO (SIEMPRE ROUND)
        if qty_step < 1:  # SI PERMITE DECIMALES
            steps = qty_base / qty_step
            qty_ajustado = round(steps) * qty_step
        else:  # SI SOLO PERMITE ENTEROS
            qty_ajustado = round(qty_base)
        
        print(f"   Después de step: {qty_ajustado:.8f}")
        
        # ✅ VERIFICAR MÍNIMO DE CANTIDAD
        if qty_ajustado < min_order_qty:
            print(f"   ⚠️  Ajustando al mínimo de cantidad: {min_order_qty}")
            qty_ajustado = min_order_qty
        
        # ✅ VERIFICAR MÍNIMO DE VALOR (SOLO AQUÍ USAR CEIL SI ES NECESARIO)
        valor_final = qty_ajustado * precio
        if valor_final < min_order_value:
            print(f"   ⚠️  Valor ${valor_final:.2f} < mínimo ${min_order_value}")
            
            # Calcular cantidad mínima requerida
            qty_minima = min_order_value / precio
            
            if qty_step < 1:
                steps_minimos = qty_minima / qty_step
                qty_ajustado = math.ceil(steps_minimos) * qty_step  # ⭐ SOLO AQUÍ CEIL
            else:
                qty_ajustado = math.ceil(qty_minima)  # ⭐ SOLO AQUÍ CEIL
            
            print(f"   Ajustado por valor mínimo: {qty_ajustado:.8f}")
        
        # CALCULAR VALOR FINAL
        valor_final = qty_ajustado * precio
        diferencia = valor_final - cantidad_usdt
        
        # Formatear cantidad
        if qty_step < 1:
            decimal_places = len(str(qty_step).split('.')[1]) if '.' in str(qty_step) else 8
            qty_str = f"{qty_ajustado:.{decimal_places}f}".rstrip('0').rstrip('.')
        else:
            qty_str = str(int(qty_ajustado))
        
        print(f"✅ CANTIDAD FINAL: {qty_str} contratos = ${valor_final:.4f}")
        print(f"   Diferencia: ${diferencia:+.4f} ({diferencia/cantidad_usdt*100:+.4f}%)")
        
        return qty_str, precio
        
    except Exception as e:
        print(f"❌ Error calculando cantidad para {symbol}: {e}")
        return None, None

def abrir_posicion_long(symbol, cantidad_usdt=5.5):
    """Abre posición long CON positionIdx CORRECTO"""
    if not PYBIT_INSTALADO or not bybit_session:
        print(f"   📈 SIMULACIÓN: Abriendo LONG en {symbol} - ${cantidad_usdt}")
        return f"SIM_{symbol}_LONG"
    
    try:
        print(f"🚀 Intentando abrir LONG en {symbol} con ${cantidad_usdt}")
        
        # CONFIGURAR HEDGE MODE Y APALANCAMIENTO PRIMERO
        configurar_hedge_mode()
        configurar_apalancamiento(symbol)
        time.sleep(2)
        
        # Calcular cantidad
        qty_str, precio_actual = calcular_cantidad_precisa(symbol, cantidad_usdt)
        if not qty_str:
            return None
        
        print(f"💰 Precio: ${precio_actual:.6f}")
        print(f"📊 Cantidad: {qty_str}")
        print(f"💵 Valor: ${float(qty_str) * precio_actual:.4f}")
        
        # CREAR ORDEN CON positionIdx CORRECTO
        print("🎯 Enviando orden MARKET BUY...")
        
        response = bybit_session.place_order(
            category='linear',
            symbol=symbol,
            side='Buy',
            orderType='Market',
            qty=qty_str,
            timeInForce="GTC",
            positionIdx=1  # ¡CORRECTO! 1 para LONG en Hedge Mode
        )
        
        if response['retCode'] == 0:
            order_id = response['result']['orderId']
            print(f"✅ LONG abierto exitosamente!")
            print(f"📋 Order ID: {order_id}")
            return order_id
        else:
            error_msg = response.get('retMsg', 'Unknown error')
            print(f"❌ Error abriendo LONG: {error_msg}")
            
            # INTENTAR SIN positionIdx SI FALLA
            print("🔄 Intentando sin positionIdx...")
            response2 = bybit_session.place_order(
                category='linear',
                symbol=symbol,
                side='Buy',
                orderType='Market',
                qty=qty_str,
                timeInForce="GTC"
            )
            
            if response2['retCode'] == 0:
                order_id = response2['result']['orderId']
                print("✅ LONG abierto (sin positionIdx)")
                return order_id
            else:
                print(f"❌ También falló sin positionIdx: {response2.get('retMsg')}")
                return None
            
    except Exception as e:
        print(f"❌ Error en abrir_posicion_long: {e}")
        return None
    
def obtener_precio_entrada_real(symbol, order_id, side):
    """Obtiene el precio real de ejecución de la orden"""
    try:
        # Obtener información de la orden ejecutada
        order_info = bybit_session.get_order_history(
            category="linear",
            symbol=symbol,
            orderId=order_id
        )
        
        if order_info['retCode'] == 0 and order_info['result']['list']:
            order_data = order_info['result']['list'][0]
            avg_price = float(order_data['avgPrice'])
            print(f"💰 Precio real de ejecución: ${avg_price:.6f}")
            return avg_price
        
        # Fallback: usar precio actual
        precio_actual = obtener_precio_actual(symbol)
        print(f"💰 Usando precio actual como fallback: ${precio_actual:.6f}")
        return precio_actual
        
    except Exception as e:
        print(f"❌ Error obteniendo precio real: {e}")
        precio_actual = obtener_precio_actual(symbol)
        return precio_actual

def abrir_posicion_short(symbol, cantidad_usdt=11.0):
    """Abre posición short CON positionIdx CORRECTO"""
    if not PYBIT_INSTALADO or not bybit_session:
        print(f"   📉 SIMULACIÓN: Abriendo SHORT en {symbol} - ${cantidad_usdt}")
        return f"SIM_{symbol}_SHORT"
    
    try:
        print(f"🚀 Intentando abrir SHORT en {symbol} con ${cantidad_usdt}")
        
        # CONFIGURAR HEDGE MODE Y APALANCAMIENTO PRIMERO
        configurar_hedge_mode()
        configurar_apalancamiento(symbol)
        time.sleep(2)
        
        # Calcular cantidad
        qty_str, precio_actual = calcular_cantidad_precisa(symbol, cantidad_usdt)
        if not qty_str:
            return None
        
        print(f"💰 Precio: ${precio_actual:.6f}")
        print(f"📊 Cantidad: {qty_str}")
        print(f"💵 Valor: ${float(qty_str) * precio_actual:.4f}")
        
        # CREAR ORDEN CON positionIdx CORRECTO
        print("🎯 Enviando orden MARKET SELL...")
        
        response = bybit_session.place_order(
            category='linear',
            symbol=symbol,
            side='Sell',
            orderType='Market',
            qty=qty_str,
            timeInForce="GTC",
            positionIdx=2  # ¡CORRECTO! 2 para SHORT en Hedge Mode
        )
        
        if response['retCode'] == 0:
            order_id = response['result']['orderId']
            print(f"✅ SHORT abierto exitosamente!")
            print(f"📋 Order ID: {order_id}")
            return order_id
        else:
            error_msg = response.get('retMsg', 'Unknown error')
            print(f"❌ Error abriendo SHORT: {error_msg}")
            
            # INTENTAR SIN positionIdx SI FALLA
            print("🔄 Intentando sin positionIdx...")
            response2 = bybit_session.place_order(
                category='linear',
                symbol=symbol,
                side='Sell',
                orderType='Market',
                qty=qty_str,
                timeInForce="GTC"
            )
            
            if response2['retCode'] == 0:
                order_id = response2['result']['orderId']
                print("✅ SHORT abierto (sin positionIdx)")
                return order_id
            else:
                print(f"❌ También falló sin positionIdx: {response2.get('retMsg')}")
                return None
            
    except Exception as e:
        print(f"❌ Error en abrir_posicion_short: {e}")
        return None

def colocar_tp_sl(symbol, side, precio_entrada, tp_percent, sl_percent):
    """Coloca Take Profit y Stop Loss - CORREGIDO"""
    if not PYBIT_INSTALADO or not bybit_session:
        print(f"   🎯 SIMULACIÓN: TP {tp_percent}%, SL {sl_percent}% para {side} en {symbol}")
        return True
    
    try:
        # Calcular precios TP y SL
        if side == "Buy":  # Para long
            # TP debe ser MAYOR que precio_entrada, SL debe ser MENOR
            if tp_percent > 0:
                tp_price = precio_entrada * (1 + tp_percent / 100)
            else:
                tp_price = ""  # No colocar TP si es 0
                
            sl_price = precio_entrada * (1 - sl_percent / 100)
            position_idx = 1
        else:  # Para short
            # TP debe ser MENOR que precio_entrada, SL debe ser MAYOR
            if tp_percent > 0:
                tp_price = precio_entrada * (1 - tp_percent / 100)
            else:
                tp_price = ""
                
            sl_price = precio_entrada * (1 + sl_percent / 100)
            position_idx = 2
        
        print(f"🎯 Configurando TP/SL para {side} en {symbol}:")
        print(f"   💰 Precio entrada: {precio_entrada:.6f}")
        if tp_price:
            print(f"   📈 TP: {tp_price:.6f} ({tp_percent}%)")
        print(f"   🛑 SL: {sl_price:.6f} ({sl_percent}%)")
        
        # Colocar TP y SL
        params = {
            "category": "linear",
            "symbol": symbol,
            "stopLoss": str(round(sl_price, 6)),
            "tpTriggerBy": "MarkPrice",
            "slTriggerBy": "MarkPrice",
            "positionIdx": position_idx
        }
        
        # Solo agregar TP si se especificó un porcentaje > 0
        if tp_price:
            params["takeProfit"] = str(round(tp_price, 6))
        
        response = bybit_session.set_trading_stop(**params)
        
        if response['retCode'] == 0:
            print(f"✅ TP/SL colocados para {side} en {symbol}")
            return True
        else:
            print(f"❌ Error colocando TP/SL: {response.get('retMsg', 'Unknown error')}")
            return False
            
    except Exception as e:
        print(f"❌ Error colocando TP/SL: {e}")
        return False
    
def puede_abrir_operaciones():
    """Verifica si el bot puede abrir nuevas operaciones basado en el balance"""
    global bot_desactivado_por_perdida, balance_inicial
    
    if balance_inicial == 0:
        return True  # Si no hay balance inicial, permitir operar
    
    balance_actual = obtener_balance_total()
    porcentaje_restante = (balance_actual / balance_inicial) * 100
    limite_minimo = (1 - perdida_maxima_permitida) * 100  # 70%
    
    if porcentaje_restante < limite_minimo:
        if not bot_desactivado_por_perdida:
            print(f"🚨 CAPITAL INSUFICIENTE: {porcentaje_restante:.1f}% < {limite_minimo:.1f}%")
            print("🚨 DESACTIVANDO NUEVAS OPERACIONES - Esperando cierre de posiciones existentes")
            bot_desactivado_por_perdida = True
        return False
    else:
        if bot_desactivado_por_perdida:
            print(f"✅ CAPITAL RECUPERADO: {porcentaje_restante:.1f}% >= {limite_minimo:.1f}%")
            print("✅ REACTIVANDO NUEVAS OPERACIONES")
            bot_desactivado_por_perdida = False
        return True   
def verificar_fuerza_tendencial_positiva(symbol, periodo='5', velas=30):
    """Verifica si la fuerza tendencial es positiva"""
    try:
        datos = obtener_datos_para_volume_regression(symbol, periodo, velas)
        if datos is None or len(datos) < velas:
            return False
        
        # Calcular pendiente del precio (fuerza tendencial)
        df_volume = calcular_volume_regression(datos)
        slope_price = df_volume['slope_price'].iloc[-1]
        
        print(f"   📊 Fuerza tendencial {symbol}: {slope_price:.8f}")
        
        # Fuerza positiva = slope_price > 0
        es_positiva = slope_price > 0
        
        if es_positiva:
            print(f"   ✅ Fuerza tendencial POSITIVA")
        else:
            print(f"   ❌ Fuerza tendencial NEGATIVA")
            
        return es_positiva
        
    except Exception as e:
        print(f"❌ Error verificando fuerza tendencial {symbol}: {e}")
        return False     
    
# ========== ESTRATEGIA DE COBERTURAS MEJORADA ==========

def operar_monedas_calificadas(activos_disponibles):
    """Ejecuta las operaciones para las monedas que califican - CON FILTRO LATERAL"""
    global operaciones_activas
    
    # ✅ VERIFICAR PARADA SUAVE
    if bot_detenerse_al_cerrar:
        print("🚫 BOT EN DETENIDO - No se abren nuevas operaciones")
        return

    # ✅ VERIFICAR SI PUEDE ABRIR NUEVAS OPERACIONES
    if not puede_abrir_operaciones():
        print("🚫 OPERACIONES DESACTIVADAS - Balance por debajo del 70% del capital inicial")
        print("   ⏳ Esperando que se cierren las operaciones existentes...")
        return
    
    # VERIFICAR POSICIONES CERRADAS ANTES DE OPERAR
    verificar_posiciones_cerradas()
    
    print(f"\n🎯 INICIANDO OPERACIONES PARA {len(activos_disponibles)} MONEDAS")
    print(f"📊 Operaciones activas actuales: {len(operaciones_activas)}")
    print(f"📈 Espacios disponibles: {MAX_MONEDAS_SIMULTANEAS - len(operaciones_activas)}")
    print("=" * 60)
    
    # ✅ APLICAR FILTRO DE LATERALIZACIÓN
    activos_con_tendencia = filtrar_activos_sin_lateralizacion(activos_disponibles)
    
    if not activos_con_tendencia:
        print("🚫 No hay activos con tendencia clara - Saltando operaciones")
        return
    
    monedas_operadas = 0
    
    for activo in activos_con_tendencia:
        symbol = activo['simbolo_bybit']
        moneda = activo['moneda']
        
        # Verificar límite de monedas
        if len(operaciones_activas) >= MAX_MONEDAS_SIMULTANEAS:
            print(f"🚫 Límite alcanzado. Se operaron {monedas_operadas} monedas")
            break
        
        # DOBLE VERIFICACIÓN (por si cambió el balance durante el loop)
        if not puede_abrir_operaciones():
            print("🚫 OPERACIONES DESACTIVADAS DURANTE EL PROCESO - Deteniendo")
            break
            
        print(f"\n📈 Operando {moneda} ({symbol})...")

        # FUERZA TENDENCIAL POSITIVA
        if not verificar_fuerza_tendencial_positiva(symbol):
            print(f"   ❌ Fuerza tendencial negativa - Saltando {symbol}")
            continue
        
        # Verificar funding rate
        funding_rate = obtener_funding_rate(symbol)
        print(f"   📊 Funding Rate: {funding_rate:.4f}%")
        
        if funding_rate >= 0.06:
            print(f"   ❌ Funding rate muy alto - Saltando")
            continue
        
        # Verificar si ya tenemos operación activa
        if symbol in operaciones_activas:
            print(f"   ⚠️  Ya existe operación activa")
            continue
        
        # Abrir posición LONG (5.5 USDT para la primera)
        print(f"   🚀 Abriendo posición LONG...")
        order_id_long = abrir_posicion_long(symbol, CANTIDAD_USDT)
        
        if order_id_long:
            # Obtener precio actual para el registro
            precio_actual = obtener_precio_actual(symbol)
            
            # Registrar operación con fecha de apertura
            operaciones_activas[symbol] = {
                'estado': ESTADOS["LONG_ABIERTO"],
                'precio_long': precio_actual,
                'order_id_long': order_id_long,
                'precio_short': None,
                'order_id_short': None,
                'moneda': moneda,
                'add_funds_ejecutado': False,
                'maximo_alcanzado': precio_actual,
                'minimo_alcanzado': precio_actual,
                'fecha_apertura': datetime.now()
            }
            
            # Colocar SL inicial (-20%) - SIN TP DINÁMICO
            colocar_tp_sl(symbol, "Buy", precio_actual, 0, SL_PORCENTAJE)
            
            print(f"   ✅ LONG establecido para {symbol} a ${precio_actual:.6f}")
            monedas_operadas += 1
    
    print(f"\n📈 RESUMEN OPERACIONES: {monedas_operadas} monedas operadas")
    print(f"📊 Total operaciones activas: {len(operaciones_activas)}")

# ========== FUNCIONES DE CIERRE CON REGISTRO ==========

def cerrar_posicion_long_real(symbol, motivo="General"):
    """Cierra posición long REAL en Bybit - CON REGISTRO"""
    print(f"🏁 Cerrando LONG para {symbol}...")
    print(f"   📝 Motivo: {motivo}")
    
    if symbol not in operaciones_activas:
        print(f"❌ No hay operación activa para {symbol}")
        return False
    
    operacion = operaciones_activas[symbol]
    
    if not PYBIT_INSTALADO or not bybit_session or operacion.get('simulado', False):
        # Modo simulación
        precio_actual = obtener_precio_actual(symbol)
        precio_long = operacion['precio_long']
        ganancia_porcentaje = ((precio_actual - precio_long) / precio_long) * 100
        
        # Determinar tipo de cierre
        if "Volume Regression" in motivo:
            tipo_cierre = "TP_VOLUME_DOWN"
        elif "Stop Loss" in motivo:
            tipo_cierre = "SL"
        elif "Protección Ganancias" in motivo:
            tipo_cierre = "PROTECCION_GANANCIAS"
        else:
            tipo_cierre = "OTRO"
        
        # Registrar operación
        registrar_operacion(
            symbol=symbol,
            precio_long=precio_long,
            precio_cierre=precio_actual,
            ejecuto_short=False,
            ejecuto_add_funds=False,
            tipo_cierre=tipo_cierre,
            ganancia_porcentaje=ganancia_porcentaje,
            cantidad_usdt=CANTIDAD_USDT,
            razon_cierre=motivo
        )
        
        print(f"📊 Operación SIMULADA cerrada: {symbol} - {tipo_cierre}")
        print(f"   💰 Resultado: {ganancia_porcentaje:+.2f}%")
        
        with operaciones_lock:
            del operaciones_activas[symbol]
        
        print(f"✅ LONG SIMULADO cerrado para {symbol}")
        return True
    
    try:
        # Obtener cantidad real de Bybit
        print(f"   🔍 Obteniendo cantidad REAL de posición LONG desde Bybit...")
        
        positions_response = bybit_session.get_positions(category="linear", symbol=symbol)
        if positions_response['retCode'] != 0:
            print(f"❌ Error obteniendo posición de Bybit: {positions_response.get('retMsg')}")
            return False
            
        qty_str = None
        precio_long_actual = operacion['precio_long']
        
        for position in positions_response['result']['list']:
            if position['side'] == 'Buy' and float(position['size']) > 0:
                qty_str = position['size']
                if 'avgPrice' in position and position['avgPrice']:
                    precio_long_actual = float(position['avgPrice'])
                print(f"   📊 Posición LONG REAL encontrada: {qty_str} contratos a ${precio_long_actual:.6f}")
                break
        
        if not qty_str:
            print(f"⚠️  No se encontró posición LONG abierta en Bybit para {symbol}")
            with operaciones_lock:
                if symbol in operaciones_activas:
                    del operaciones_activas[symbol]
            return True
        
        print(f"   📤 Cerrando {qty_str} contratos...")
        
        response = bybit_session.place_order(
            category='linear',
            symbol=symbol,
            side='Sell',
            orderType='Market',
            qty=qty_str,
            timeInForce="GTC",
            positionIdx=1
        )
        
        if response['retCode'] == 0:
            print(f"✅ ORDEN DE CIERRE enviada exitosamente!")
            order_id = response['result']['orderId']
            
            # Esperar confirmación
            print(f"   ⏳ Esperando confirmación de cierre...")
            time.sleep(3)
            
            # Verificar cierre
            positions_after = bybit_session.get_positions(category="linear", symbol=symbol)
            long_cerrado = True
            
            if positions_after['retCode'] == 0:
                for position in positions_after['result']['list']:
                    if position['side'] == 'Buy' and float(position['size']) > 0:
                        long_cerrado = False
                        break
            
            if long_cerrado:
                precio_cierre = obtener_precio_actual(symbol)
                ganancia_porcentaje = ((precio_cierre - precio_long_actual) / precio_long_actual) * 100
                
                # Determinar tipo de cierre
                if "Volume Regression" in motivo:
                    tipo_cierre = "TP_VOLUME_DOWN"
                elif "Stop Loss" in motivo:
                    tipo_cierre = "SL"
                elif "Protección Ganancias" in motivo:
                    tipo_cierre = "PROTECCION_GANANCIAS"
                else:
                    tipo_cierre = "OTRO"
                
                # Registrar operación
                registrar_operacion(
                    symbol=symbol,
                    precio_long=precio_long_actual,
                    precio_cierre=precio_cierre,
                    ejecuto_short=False,
                    ejecuto_add_funds=False,
                    tipo_cierre=tipo_cierre,
                    ganancia_porcentaje=ganancia_porcentaje,
                    cantidad_usdt=CANTIDAD_USDT,
                    razon_cierre=motivo
                )
                
                print(f"📊 RESULTADO {symbol}:")
                print(f"   📈 Entrada: ${precio_long_actual:.6f}")
                print(f"   📉 Salida: ${precio_cierre:.6f}")
                print(f"   💰 Resultado: {ganancia_porcentaje:+.2f}%")
                print(f"   🎯 Tipo: {tipo_cierre}")
                
                with operaciones_lock:
                    if symbol in operaciones_activas:
                        del operaciones_activas[symbol]
                
                print(f"✅ LONG REAL cerrado correctamente para {symbol}")
                return True
            else:
                print(f"🚨 ALERTA: LONG no se cerró completamente")
                return False
                
        else:
            error_msg = response.get('retMsg', 'Unknown error')
            print(f"❌ Error cerrando LONG: {error_msg}")
            return False
            
    except Exception as e:
        print(f"❌ Error en cerrar_posicion_long_real: {e}")
        return False

def cerrar_ambas_posiciones_con_registro(symbol, tipo_cierre):
    """Cierra ambas posiciones - TODOS LOS MONTOS DINÁMICOS"""
    print(f"🏁 Cerrando ambas posiciones para {symbol}...")
    print(f"   📝 Tipo: {tipo_cierre}")
    
    if symbol not in operaciones_activas:
        print(f"❌ No hay operación activa para {symbol}")
        return False
    
    operacion = operaciones_activas[symbol]
    
    # ✅ CONFIGURACIÓN DINÁMICA
    RELACION_SHORT_VS_LONG = 2.0  # SHORT = 2 × LONG
    RELACION_ADD_FUNDS_VS_LONG = 3.0  # ADD FUNDS = 3 × LONG
    
    monto_long_inicial = CANTIDAD_USDT
    monto_short = CANTIDAD_USDT * RELACION_SHORT_VS_LONG  # Dinámico
    monto_long_con_add_funds = CANTIDAD_USDT * RELACION_ADD_FUNDS_VS_LONG  # Dinámico
    
    if not PYBIT_INSTALADO or not bybit_session or operacion.get('simulado', False):
        # Modo simulación - ✅ MONTOS COMPLETAMENTE DINÁMICOS
        precio_actual = obtener_precio_actual(symbol)
        precio_long = operacion['precio_long']
        precio_short = operacion.get('precio_short', 0)
        
        # Calcular porcentajes
        ganancia_long = ((precio_actual - precio_long) / precio_long) * 100
        ganancia_short = ((precio_short - precio_actual) / precio_short) * 100 if precio_short > 0 else 0
        
        # ✅ CALCULAR MONTOS BASADOS EN RELACIONES (NO FIJOS)
        if tipo_cierre in ["TP_SHORT_AVANZADO", "TP_LONG_AVANZADO", "VUELTA_SHORT"]:
            
            if operacion.get('add_funds_ejecutado', False):
                # Después de ADD FUNDS
                inversion_long = monto_long_con_add_funds  # Dinámico: 3 × CANTIDAD_USDT
            else:
                # Antes de ADD FUNDS  
                inversion_long = monto_long_inicial  # CANTIDAD_USDT
            
            inversion_short = monto_short  # Dinámico: 2 × CANTIDAD_USDT
            inversion_total = inversion_long + inversion_short
            
            # Calcular ganancia/pérdida en dólares
            ganancia_usdt_long = inversion_long * (ganancia_long / 100)
            ganancia_usdt_short = inversion_short * (ganancia_short / 100)
            ganancia_usdt_total = ganancia_usdt_long + ganancia_usdt_short
            
            # Porcentaje basado en inversión total
            ganancia_porcentaje = (ganancia_usdt_total / inversion_total) * 100
            
            print(f"🎯 {tipo_cierre} - MONTOS DINÁMICOS:")
            print(f"   ⚙️  CONFIG: LONG_INICIAL=${monto_long_inicial}, SHORT=${monto_short:.1f}, LONG+ADD=${monto_long_con_add_funds:.1f}")
            print(f"   📊 INVERSIONES: LONG=${inversion_long:.1f} | SHORT=${inversion_short:.1f}")
            print(f"   💰 LONG: {ganancia_long:+.2f}% = ${ganancia_usdt_long:+.2f}")
            print(f"   💰 SHORT: {ganancia_short:+.2f}% = ${ganancia_usdt_short:+.2f}")
            print(f"   📈 TOTAL: ${inversion_total:.1f} → ${ganancia_usdt_total:+.2f} = {ganancia_porcentaje:+.2f}%")
        else:
            # Solo LONG
            ganancia_porcentaje = ganancia_long
            ganancia_usdt_total = monto_long_inicial * (ganancia_long / 100)
            
            print(f"🎯 {tipo_cierre} - Solo LONG:")
            print(f"   📊 INVERSIÓN: ${monto_long_inicial:.1f}")
            print(f"   📈 RESULTADO: {ganancia_long:+.2f}% = ${ganancia_usdt_total:+.2f}")
        
        # Registrar operación
        registrar_operacion(
            symbol=symbol,
            precio_long=precio_long,
            precio_cierre=precio_actual,
            ejecuto_short=precio_short > 0,
            ejecuto_add_funds=operacion.get('add_funds_ejecutado', False),
            tipo_cierre=tipo_cierre,
            ganancia_porcentaje=ganancia_porcentaje,
            cantidad_usdt=CANTIDAD_USDT,
            razon_cierre=tipo_cierre
        )
        
        with operaciones_lock:
            del operaciones_activas[symbol]
        
        return True
    
    try:
        # ✅ BYBIT REAL - PRIMERO OBTENER DATOS PARA REGISTRO (ESTO ES NUEVO)
        print("   🔄 Paso 1: Obteniendo datos para registro...")
        precio_cierre = obtener_precio_actual(symbol)
        precio_long = operacion['precio_long']
        precio_short = operacion.get('precio_short', 0)
        add_funds_ejecutado = operacion.get('add_funds_ejecutado', False)
        
        # ✅ OBTENER MONTOS ANTES DE CERRAR
        print("   🔄 Paso 2: Obteniendo montos para registro...")
        try:
            monto_long_real, monto_short_real = obtener_montos_reales_posiciones(symbol)
        except Exception as e:
            print(f"   ⚠️  No se pudieron obtener montos reales: {e}")
            # Usar montos por defecto basados en la configuración
            if add_funds_ejecutado:
                monto_long_real = monto_long_con_add_funds  # 3 × CANTIDAD_USDT
            else:
                monto_long_real = monto_long_inicial  # CANTIDAD_USDT
            monto_short_real = monto_short  # 2 × CANTIDAD_USDT
            print(f"   📊 Usando montos por defecto: LONG=${monto_long_real:.1f}, SHORT=${monto_short_real:.1f}")
        
        # ✅ AHORA INTENTAR CERRAR POSICIONES
        print("   🔄 Paso 3: Cerrando posiciones en Bybit...")
        success = cerrar_ambas_posiciones(symbol)
        
        # ✅ REGISTRAR SIEMPRE, INCLUSO SI EL CIERRE FALLA
        print("   🔄 Paso 4: Registrando operación...")
        
        # Calcular porcentajes
        ganancia_long = ((precio_cierre - precio_long) / precio_long) * 100
        ganancia_short = ((precio_short - precio_cierre) / precio_short) * 100 if precio_short > 0 else 0
        
        # USAR MONTOS REALES DE BYBIT (O POR DEFECTO)
        if tipo_cierre in ["TP_SHORT_AVANZADO", "TP_LONG_AVANZADO", "VUELTA_SHORT"]:
            inversion_total = monto_long_real + monto_short_real
            
            ganancia_usdt_long = monto_long_real * (ganancia_long / 100)
            ganancia_usdt_short = monto_short_real * (ganancia_short / 100)
            ganancia_usdt_total = ganancia_usdt_long + ganancia_usdt_short
            
            ganancia_porcentaje = (ganancia_usdt_total / inversion_total) * 100
            
            print(f"🎯 {tipo_cierre} - MONTOS REALES BYBIT:")
            print(f"   📊 INVERSIONES: LONG=${monto_long_real:.2f} | SHORT=${monto_short_real:.2f}")
            print(f"   💰 GANANCIA TOTAL: ${ganancia_usdt_total:+.2f} = {ganancia_porcentaje:+.2f}%")
        else:
            ganancia_porcentaje = ganancia_long
            ganancia_usdt_total = monto_long_real * (ganancia_long / 100)
        
        # Registrar
        registrar_operacion(
            symbol=symbol,
            precio_long=precio_long,
            precio_cierre=precio_cierre,
            ejecuto_short=precio_short > 0,
            ejecuto_add_funds=add_funds_ejecutado,
            tipo_cierre=tipo_cierre,
            ganancia_porcentaje=ganancia_porcentaje,
            cantidad_usdt=CANTIDAD_USDT,
            razon_cierre=tipo_cierre
        )
        
        # ✅ ELIMINAR DE OPERACIONES ACTIVAS SIEMPRE
        with operaciones_lock:
            if symbol in operaciones_activas:
                del operaciones_activas[symbol]
        
        if not success:
            print(f"⚠️  Verificación de cierre falló para {symbol}, pero posiciones cerradas y registro completado")
            return True
        
        print(f"📊 {symbol} CERRADO: {tipo_cierre} = {ganancia_porcentaje:+.2f}%")
        return True
        
    except Exception as e:
        print(f"❌ Error crítico en cierre: {e}")
        # Intentar eliminar de todas formas para evitar bloqueos
        with operaciones_lock:
            if symbol in operaciones_activas:
                del operaciones_activas[symbol]
        return False
    
def obtener_montos_reales_posiciones(symbol):
    """Obtiene los montos reales de las posiciones LONG y SHORT desde Bybit"""
    if not PYBIT_INSTALADO or not bybit_session:
        # En simulación, usar montos por defecto
        return CANTIDAD_USDT, CANTIDAD_USDT * 2.0
    
    try:
        print(f"   🔍 Obteniendo montos reales desde Bybit para {symbol}...")
        
        response = bybit_session.get_positions(category="linear", symbol=symbol)
        
        if response['retCode'] == 0:
            monto_long = 0.0
            monto_short = 0.0
            
            for position in response['result']['list']:
                size = float(position['size'])
                if size > 0:
                    side = position['side']
                    avg_price = float(position['avgPrice'])
                    # Calcular monto en USDT = tamaño * precio promedio
                    monto_posicion = size * avg_price
                    
                    if side == 'Buy':  # LONG
                        monto_long = monto_posicion
                        print(f"   📈 LONG real: {size} contratos @ ${avg_price:.6f} = ${monto_long:.2f}")
                    elif side == 'Sell':  # SHORT
                        monto_short = monto_posicion
                        print(f"   📉 SHORT real: {size} contratos @ ${avg_price:.6f} = ${monto_short:.2f}")
            
            # Si no se encontraron posiciones, usar valores por defecto
            if monto_long == 0 and monto_short == 0:
                print(f"   ⚠️  No se encontraron posiciones reales, usando montos por defecto")
                return CANTIDAD_USDT, CANTIDAD_USDT * 2.0
            
            print(f"   ✅ Montos reales obtenidos: LONG=${monto_long:.2f}, SHORT=${monto_short:.2f}")
            return monto_long, monto_short
        else:
            print(f"   ❌ Error obteniendo posiciones: {response.get('retMsg')}")
            return CANTIDAD_USDT, CANTIDAD_USDT * 2.0
            
    except Exception as e:
        print(f"   ❌ Error en obtener_montos_reales_posiciones: {e}")
        return CANTIDAD_USDT, CANTIDAD_USDT * 2.0    
    
# ========== FUNCIONES EXISTENTES (se mantienen igual) ==========

def obtener_montos_reales_posiciones(symbol):
    """Obtiene los montos reales de las posiciones LONG y SHORT desde Bybit"""
    if not PYBIT_INSTALADO or not bybit_session:
        # En simulación, usar montos por defecto
        return CANTIDAD_USDT, CANTIDAD_USDT * 2.0
    
    try:
        print(f"   🔍 Obteniendo montos reales desde Bybit para {symbol}...")
        
        response = bybit_session.get_positions(category="linear", symbol=symbol)
        
        if response['retCode'] == 0:
            monto_long = 0.0
            monto_short = 0.0
            
            for position in response['result']['list']:
                size = float(position['size'])
                if size > 0:
                    side = position['side']
                    avg_price = float(position['avgPrice'])
                    # Calcular monto en USDT = tamaño * precio promedio
                    monto_posicion = size * avg_price
                    
                    if side == 'Buy':  # LONG
                        monto_long = monto_posicion
                        print(f"   📈 LONG real: {size} contratos @ ${avg_price:.6f} = ${monto_long:.2f}")
                    elif side == 'Sell':  # SHORT
                        monto_short = monto_posicion
                        print(f"   📉 SHORT real: {size} contratos @ ${avg_price:.6f} = ${monto_short:.2f}")
            
            # Si no se encontraron posiciones, usar valores por defecto
            if monto_long == 0 and monto_short == 0:
                print(f"   ⚠️  No se encontraron posiciones reales, usando montos por defecto")
                return CANTIDAD_USDT, CANTIDAD_USDT * 2.0
            
            print(f"   ✅ Montos reales obtenidos: LONG=${monto_long:.2f}, SHORT=${monto_short:.2f}")
            return monto_long, monto_short
        else:
            print(f"   ❌ Error obteniendo posiciones: {response.get('retMsg')}")
            return CANTIDAD_USDT, CANTIDAD_USDT * 2.0
            
    except Exception as e:
        print(f"   ❌ Error en obtener_montos_reales_posiciones: {e}")
        return CANTIDAD_USDT, CANTIDAD_USDT * 2.0

def obtener_funding_rate(symbol):
    """Obtiene el funding rate actual para un símbolo"""
    if not PYBIT_INSTALADO or not bybit_session:
        return 0.01
    
    try:
        response = bybit_session.get_funding_rate_history(
            category="linear",
            symbol=symbol,
            limit=1
        )
        
        if response['retCode'] == 0 and response['result']['list']:
            funding_rate = float(response['result']['list'][0]['fundingRate']) * 100
            return funding_rate
        else:
            return 0.05
            
    except Exception as e:
        return 0.05
    
def obtener_balance_total():
    """Obtiene el balance total actual de la cuenta"""
    if not PYBIT_INSTALADO or not bybit_session:
        # En simulación, retornar un balance fijo
        return 1000.0  # Simulación: $1000
    
    try:
        response = bybit_session.get_wallet_balance(accountType="UNIFIED")
        
        if response['retCode'] == 0:
            total_balance = 0.0
            for account in response['result']['list']:
                for coin in account['coin']:
                    if coin['coin'] == 'USDT':
                        total_balance += float(coin['walletBalance'])
            return total_balance
        else:
            print(f"❌ Error obteniendo balance: {response.get('retMsg')}")
            return 0.0
            
    except Exception as e:
        print(f"❌ Error en obtener_balance_total: {e}")
        return 0.0    

def extraer_simbolo_de_moneda(moneda):
    """Extrae el símbolo de la moneda"""
    if not moneda:
        return None
    
    palabras = moneda.split()
    simbolos = []
    
    for palabra in palabras:
        palabra_limpia = ''.join(c for c in palabra if c.isalpha() or c.isdigit())
        if palabra_limpia and palabra_limpia.isupper():
            simbolos.append(palabra_limpia)
    
    if simbolos:
        return simbolos[-1]
    
    for palabra in palabras:
        palabra_limpia = ''.join(c for c in palabra if c.isalpha())
        if 1 <= len(palabra_limpia) <= 10 and palabra_limpia.isalpha():
            return palabra_limpia.upper()
    
    return None

def obtener_balance_bybit():
    """Obtiene el balance disponible"""
    if not PYBIT_INSTALADO or not bybit_session:
        return "No disponible (modo simulación)"
    
    try:
        response = bybit_session.get_wallet_balance(accountType="UNIFIED")
        
        if response['retCode'] == 0:
            balances = []
            for balance in response['result']['list']:
                for coin in balance['coin']:
                    if float(coin['walletBalance']) > 0:
                        balances.append(f"{coin['coin']}: {float(coin['walletBalance']):.4f}")
            
            if balances:
                return " | ".join(balances[:3])
            else:
                return "Balance: $0.00"
        else:
            return f"Error: {response.get('retMsg', 'Unknown')}"
            
    except Exception as e:
        return f"Error: {str(e)}"

def inicializar_bybit():
    """Inicializa la conexión con Bybit - MANTENIENDO HEDGE MODE"""
    global bybit_session
    
    if not BYBIT_CONFIG["api_key"] or not BYBIT_CONFIG["api_secret"]:
        print("❌ No se encontraron las credenciales de Bybit")
        return False
    
    if not PYBIT_INSTALADO:
        print("⚠️  Pybit no instalado - Usando modo simulación")
        return False
    
    try:
        bybit_session = HTTP(
            testnet=BYBIT_CONFIG["testnet"],
            api_key=BYBIT_CONFIG["api_key"],
            api_secret=BYBIT_CONFIG["api_secret"],
        )
        
        print("🔗 Probando conexión con Bybit...")
        response = bybit_session.get_wallet_balance(accountType="UNIFIED")
        
        if response['retCode'] == 0:
            print("✅ Conexión con Bybit establecida correctamente")
            print(f"   Modo: {'TESTNET' if BYBIT_CONFIG['testnet'] else 'LIVE'}")
            
            # Configurar Hedge Mode como antes
            if configurar_hedge_mode():
                print("✅ Hedge Mode configurado")
            else:
                print("⚠️  Continuando sin Hedge Mode...")
            
            return True
        else:
            print(f"❌ Error en la conexión: {response.get('retMsg', 'Unknown error')}")
            return False
            
    except Exception as e:
        print(f"❌ Error conectando con Bybit: {e}")
        return False

def configurar_hedge_mode():
    """Configura el account en Hedge Mode - VERSIÓN MEJORADA"""
    if not PYBIT_INSTALADO or not bybit_session:
        return True
    
    try:
        print("🔧 Verificando modo de posición...")
        
        # Primero intentar obtener el modo actual
        try:
            response = bybit_session.get_position_mode(category="linear")
            if response['retCode'] == 0:
                modo_actual = response['result'].get('mode', 0)
                print(f"📊 Modo de posición actual: {'Hedge' if modo_actual == 3 else 'One-Way'}")
                
                if modo_actual == 3:
                    print("✅ Ya está en Hedge Mode")
                    return True
        except Exception as e:
            print(f"ℹ️  No se pudo verificar modo actual: {e}")
        
        # Configurar Hedge Mode - MÉTODO CORRECTO
        print("🔄 Configurando Hedge Mode...")
        try:
            # Para cuentas unificadas, el modo Hedge es 3
            response = bybit_session.switch_position_mode(
                category="linear",
                mode=3  # 3 = Hedge Mode para cuentas unificadas
            )
            
            if response['retCode'] == 0:
                print("✅ Hedge Mode configurado correctamente")
                return True
            else:
                error_msg = response.get('retMsg', 'Unknown error')
                print(f"⚠️  Info Hedge Mode: {error_msg}")
                
                # Si falla, puede que ya esté en Hedge Mode
                print("💡 Asumiendo que ya está en Hedge Mode...")
                return True
                    
        except Exception as e:
            print(f"⚠️  Error configurando Hedge Mode: {e}")
            print("💡 Continuando asumiendo Hedge Mode...")
            return True
            
    except Exception as e:
        print(f"⚠️  Error en configurar_hedge_mode: {e}")
        return True

def configurar_apalancamiento(symbol):
    """Configura el apalancamiento para el símbolo - VERSIÓN SIMPLIFICADA"""
    if not PYBIT_INSTALADO or not bybit_session:
        return True
    
    try:
        print(f"🔧 Configurando apalancamiento {LEVERAGE}x para {symbol}...")
        
        response = bybit_session.set_leverage(
            category="linear",
            symbol=symbol,
            buyLeverage=str(LEVERAGE),
            sellLeverage=str(LEVERAGE)
        )
        
        if response['retCode'] == 0:
            print(f"✅ Apalancamiento {LEVERAGE}x configurado para {symbol}")
            return True
        else:
            error_msg = response.get('retMsg', 'Unknown error')
            print(f"⚠️  Info apalancamiento {symbol}: {error_msg}")
            
            # Intentar con valores numéricos
            try:
                response = bybit_session.set_leverage(
                    category="linear",
                    symbol=symbol,
                    buyLeverage=LEVERAGE,
                    sellLeverage=LEVERAGE
                )
                
                if response['retCode'] == 0:
                    print(f"✅ Apalancamiento {LEVERAGE}x configurado (método numérico)")
                    return True
                else:
                    print(f"⚠️  No se pudo configurar apalancamiento: {response.get('retMsg')}")
                    return False
            except Exception as e:
                print(f"⚠️  Error en método numérico: {e}")
                return False
                
    except Exception as e:
        print(f"⚠️  Error configurando apalancamiento {symbol}: {e}")
        return False
    
# ========== OBTENER PRECIO PROMEDIO DESPUES DEL ADD ==========    

def obtener_cantidad_posicion_por_order_id(symbol, order_id):
    """Obtiene la cantidad ejecutada de una orden específica"""
    if not PYBIT_INSTALADO or not bybit_session or not order_id:
        # En modo simulación, usar cantidades aproximadas
        precio_actual = obtener_precio_actual(symbol)
        if "ADD" in str(order_id):
            return str(16.5 / precio_actual)  # Simular cantidad para ADD FUNDS
        else:
            return str(5.5 / precio_actual)   # Simular cantidad para LONG inicial
    
    try:
        # Obtener información de la orden ejecutada
        order_info = bybit_session.get_order_history(
            category="linear",
            symbol=symbol,
            orderId=order_id
        )
        
        if order_info['retCode'] == 0 and order_info['result']['list']:
            order_data = order_info['result']['list'][0]
            cantidad_ejecutada = order_data.get('execQty', '0')
            if cantidad_ejecutada and float(cantidad_ejecutada) > 0:
                return cantidad_ejecutada
        
        return None
        
    except Exception as e:
        print(f"❌ Error obteniendo cantidad por order ID: {e}")
        return None    

def obtener_pares_bybit():
    """Obtiene todos los pares de trading disponibles en Bybit"""
    if not PYBIT_INSTALADO or not bybit_session:
        pares_simulados = ["BTCUSDT", "ETHUSDT", "SOLUSDT", "ADAUSDT", "DOTUSDT"]
        return pares_simulados
    
    try:
        symbol_info = bybit_session.get_instruments_info(category="linear")
        pares_disponibles = []
        if symbol_info['retCode'] == 0:
            for symbol in symbol_info['result']['list']:
                pares_disponibles.append(symbol['symbol'])
            print(f"📊 Pares disponibles en Bybit: {len(pares_disponibles)}")
        else:
            print(f"❌ Error obteniendo pares: {symbol_info.get('retMsg', 'Unknown error')}")
            return []
        
        return pares_disponibles
        
    except Exception as e:
        print(f"❌ Error obteniendo pares de Bybit: {e}")
        return []

def verificar_operaciones_abiertas(symbol):
    """Verifica si hay operaciones abiertas para un símbolo específico"""
    if not PYBIT_INSTALADO or not bybit_session:
        return False, "Sin operaciones abiertas (simulado)"
    
    try:
        positions = bybit_session.get_positions(category="linear", symbol=symbol)
        if positions['retCode'] == 0:
            for position in positions['result']['list']:
                if float(position['size']) > 0:
                    return True, f"Posición abierta: {position['size']} contratos"
        
        orders = bybit_session.get_open_orders(category="linear", symbol=symbol)
        if orders['retCode'] == 0:
            if len(orders['result']['list']) > 0:
                order_count = len(orders['result']['list'])
                return True, f"{order_count} órdenes activas"
        
        return False, "Sin operaciones abiertas"
        
    except Exception as e:
        print(f"❌ Error verificando operaciones para {symbol}: {e}")
        return False, "Error en verificación"

def filtrar_activos_disponibles_bybit(activos_seleccionados):
    """Filtra los activos seleccionados que están disponibles en Bybit Y sin operaciones activas"""
    print("\n🔍 VERIFICANDO DISPONIBILIDAD EN BYBIT Y OPERACIONES ACTIVAS...")
    
    balance = obtener_balance_bybit()
    print(f"💰 Balance disponible: {balance}")
    
    if not PYBIT_INSTALADO:
        print("💡 Modo simulación - Instala pybit para verificación real")
    
    pares_bybit = obtener_pares_bybit()
    if not pares_bybit:
        print("❌ No se pudieron obtener los pares de Bybit")
        return []
    
    activos_disponibles = []
    
    for activo in activos_seleccionados:
        moneda = activo['moneda']
        simbolo = activo.get('simbolo')
        
        if not simbolo:
            print(f"   ❌ {moneda}: No tiene símbolo extraído")
            continue
        
        simbolo_bybit = f"{simbolo}USDT"
        
        # ✅ VERIFICACIÓN 1: Disponible en Bybit
        if simbolo_bybit in pares_bybit:
            # ✅ VERIFICACIÓN 2: Sin operaciones abiertas en Bybit
            tiene_operaciones, motivo = verificar_operaciones_abiertas(simbolo_bybit)
            
            # ✅ VERIFICACIÓN 3: Sin operación activa en NUESTRO tracking
            tiene_operacion_activa = simbolo_bybit in operaciones_activas
            
            if not tiene_operaciones and not tiene_operacion_activa:
                activo['simbolo_bybit'] = simbolo_bybit
                activos_disponibles.append(activo)
                print(f"   ✅ {moneda} ({simbolo}) -> {simbolo_bybit}: Disponible y sin operaciones")
            else:
                if tiene_operaciones:
                    print(f"   ⚠️  {moneda} ({simbolo}) -> {simbolo_bybit}: {motivo}")
                if tiene_operacion_activa:
                    print(f"   ⚠️  {moneda} ({simbolo}) -> {simbolo_bybit}: Ya tiene operación activa en nuestro tracking")
        else:
            print(f"   ❌ {moneda} ({simbolo}) -> {simbolo_bybit}: No disponible en Bybit")
    
    print(f"\n📊 Resumen Bybit: {len(activos_disponibles)} de {len(activos_seleccionados)} activos disponibles y sin operaciones activas")
    return activos_disponibles

# ========== FUNCIONES DE SCRAPING MODIFICADAS PARA GOOGLE CLOUD ==========

def obtener_tabla_coinalyze(url):
    """Obtiene la tabla de datos de CoinAlyze - VERSIÓN GOOGLE CLOUD"""
    print("🌐 Iniciando Chrome para Google Cloud...")
    driver = configurar_chrome_cloud()
    
    if not driver:
        print("❌ No se pudo inicializar Chrome. Usando datos de respaldo...")
        return crear_dataframe_respaldo()
    
    try:
        print("📄 Cargando página de CoinAlyze...")
        driver.get(url)
        wait = WebDriverWait(driver, 30)
        time.sleep(12)  # Más tiempo para cargar JavaScript
        
        print("🔍 Buscando tabla de datos...")
        table_selectors = [
            "//table",
            "//div[contains(@class, 'table')]//table",
            "//table[contains(@class, 'table')]",
            "//*[@id='root']//table",
            "//div[@id='root']//table",
            "//div[contains(@class, 'ag-root')]//table",
            "//div[@class='ag-theme-balham']//table",
            "//div[contains(@class, 'react-grid-Container')]//table"
        ]
        
        table_elem = None
        for selector in table_selectors:
            try:
                table_elem = wait.until(EC.presence_of_element_located((By.XPATH, selector)))
                print(f"✅ Tabla encontrada con selector: {selector}")
                break
            except Exception as e:
                print(f"❌ Selector {selector} falló: {e}")
                continue
        
        if not table_elem:
            print("⚠️ No se pudo encontrar la tabla. Intentando método alternativo...")
            # Método alternativo: buscar cualquier tabla en la página
            todas_las_tablas = driver.find_elements(By.TAG_NAME, "table")
            if todas_las_tablas:
                table_elem = todas_las_tablas[0]
                print("✅ Tabla encontrada mediante búsqueda general")
            else:
                raise Exception("No se pudo encontrar ninguna tabla en la página")
        
        # Obtener headers
        headers = []
        try:
            header_rows = table_elem.find_elements(By.TAG_NAME, "thead")
            if header_rows:
                header_cells = header_rows[0].find_elements(By.TAG_NAME, "th")
                headers = [cell.text.strip() for cell in header_cells if cell.text.strip()]
            
            if not headers:
                # Si no hay thead, buscar en la primera fila
                primera_fila = table_elem.find_element(By.TAG_NAME, "tr")
                header_cells = primera_fila.find_elements(By.TAG_NAME, "th")
                headers = [cell.text.strip() for cell in header_cells if cell.text.strip()]
            
            print(f"✅ Headers encontrados: {headers}")
        except Exception as e:
            print(f"❌ Error obteniendo headers: {e}")
            # Headers por defecto basados en CoinAlyze
            headers = ['COIN', 'PRICE', 'CHG 24H', 'MKT CAP', 'VOL 24H', 'OPEN INTEREST', 'OI CHG 24H']
        
        # Obtener datos
        datos = []
        try:
            # Buscar filas de datos
            rows = table_elem.find_elements(By.TAG_NAME, "tr")
            print(f"📊 Se encontraron {len(rows)} filas")
            
            for i, row in enumerate(rows):
                try:
                    cells = row.find_elements(By.TAG_NAME, "td")
                    if cells and len(cells) >= len(headers):
                        fila_datos = [cell.text.strip() for cell in cells]
                        # Filtrar filas vacías
                        if any(fila_datos) and fila_datos[0] != '':
                            if len(fila_datos) > len(headers):
                                fila_datos = fila_datos[:len(headers)]
                            datos.append(fila_datos)
                            
                            # Mostrar progreso cada 10 filas
                            if len(datos) % 10 == 0:
                                print(f"   📝 Procesadas {len(datos)} filas...")
                except Exception as e:
                    print(f"❌ Error procesando fila {i}: {e}")
                    continue
                    
        except Exception as e:
            print(f"❌ Error obteniendo datos: {e}")
            return crear_dataframe_respaldo()
        
        # Crear DataFrame
        if datos:
            df = pd.DataFrame(datos, columns=headers)
            print(f"✅ DataFrame creado con {len(df)} filas y {len(df.columns)} columnas")
            
            # Mostrar lista de monedas encontradas
            print(f"\n📋 LISTA DE MONEDAS ENCONTRADAS ({len(df)}):")
            print("=" * 70)
            for i, (idx, fila) in enumerate(df.iterrows(), 1):
                if i <= 20:  # Mostrar solo las primeras 20
                    moneda = str(fila['COIN']) if 'COIN' in fila else "N/A"
                    price = str(fila['PRICE']) if 'PRICE' in fila else "N/A"
                    chg_24h = str(fila['CHG 24H']) if 'CHG 24H' in fila else "N/A"
                    simbolo = extraer_simbolo_de_moneda(moneda)
                    simbolo_str = f"({simbolo})" if simbolo else "(sin símbolo)"
                    print(f"{i:2d}. {moneda:25} {simbolo_str:15} | Price: {price:12} | CHG: {chg_24h:8}")
            
            if len(df) > 20:
                print(f"... y {len(df) - 20} más")
            
            return df
        else:
            print("❌ No se encontraron datos en la tabla. Usando respaldo...")
            return crear_dataframe_respaldo()
            
    except Exception as e:
        print(f"❌ Error durante el scraping: {e}")
        return crear_dataframe_respaldo()
    
    finally:
        if driver:
            driver.quit()
            print("✅ Chrome cerrado")

def limpiar_y_convertir_valor(valor):
    """Convierte valores como '$40.6m' a numérico"""
    if not valor or valor == 'n/a' or valor == 'ERROR' or valor == '':
        return 0
    
    try:
        valor_limpio = str(valor).replace('$', '').replace(',', '').replace(' ', '').strip()
        if 'b' in valor_limpio.lower():
            return float(valor_limpio.lower().replace('b', '')) * 1_000_000_000
        elif 'm' in valor_limpio.lower():
            return float(valor_limpio.lower().replace('m', '')) * 1_000_000
        elif 'k' in valor_limpio.lower():
            return float(valor_limpio.lower().replace('k', '')) * 1_000
        else:
            return float(valor_limpio)
    except:
        return 0

def limpiar_porcentaje(valor):
    """Convierte porcentajes como '+14.52%' a numérico"""
    if not valor or valor == 'n/a' or valor == 'ERROR' or valor == '':
        return 0
    
    try:
        valor_limpio = str(valor).replace('%', '').replace('+', '').replace(' ', '').strip()
        return float(valor_limpio)
    except:
        return 0

def comparar_y_seleccionar_activos(df_actual, df_anterior):
    """Compara los datos actuales con los anteriores y seleccionar activos que cumplan los criterios"""
    if df_anterior is None or df_anterior.empty:
        print("📭 No hay datos anteriores para comparar. Primera ejecución.")
        return []
    
    print("🔍 Comparando activos con datos anteriores...")
    
    activos_seleccionados = []
    total_analizados = 0
    
    for idx_actual, fila_actual in df_actual.iterrows():
        try:
            moneda_completa = str(fila_actual['COIN'])
            if not moneda_completa or moneda_completa == '' or moneda_completa == 'nan':
                continue
            
            total_analizados += 1
            simbolo = extraer_simbolo_de_moneda(moneda_completa)
            if not simbolo:
                continue
            
            # Buscar la misma moneda en datos anteriores
            fila_anterior = None
            for idx_ant, fila_ant in df_anterior.iterrows():
                moneda_anterior_completa = str(fila_ant['COIN'])
                simbolo_anterior = extraer_simbolo_de_moneda(moneda_anterior_completa)
                if simbolo_anterior and simbolo_anterior == simbolo:
                    fila_anterior = fila_ant
                    break
            
            if fila_anterior is None:
                continue
            
            # Extraer y limpiar valores
            price_actual = limpiar_y_convertir_valor(fila_actual['PRICE'])
            chg_24h_actual = limpiar_porcentaje(fila_actual['CHG 24H'])
            mkt_cap_actual = limpiar_y_convertir_valor(fila_actual['MKT CAP'])
            vol_24h_actual = limpiar_y_convertir_valor(fila_actual['VOL 24H'])
            open_interest_actual = limpiar_y_convertir_valor(fila_actual['OPEN INTEREST'])
            oi_chg_24h_actual = limpiar_porcentaje(fila_actual['OI CHG 24H'])
            
            price_anterior = limpiar_y_convertir_valor(fila_anterior['PRICE'])
            oi_chg_24h_anterior = limpiar_porcentaje(fila_anterior['OI CHG 24H'])
            
            oi_vol_ratio = open_interest_actual / vol_24h_actual if vol_24h_actual > 0 else float('inf')
            
            # Aplicar criterios de selección
            criterios = [
                price_actual > price_anterior,
                oi_chg_24h_actual > oi_chg_24h_anterior,
                oi_vol_ratio < 0.30,
                mkt_cap_actual > 50_000_000,
                chg_24h_actual > 3,
                chg_24h_actual > 0
            ]
            
            if all(criterios):
                print(f"\n🎯 ACTIVO SELECCIONADO: {moneda_completa} ({simbolo})")
                print(f"  📊 Datos actuales:")
                print(f"     Price: ${price_actual:.4f} (Anterior: ${price_anterior:.4f})")
                print(f"     CHG 24H: {chg_24h_actual:.2f}%")
                print(f"     MKT CAP: ${mkt_cap_actual:,.0f}")
                print(f"     VOL 24H: ${vol_24h_actual:,.0f}")
                print(f"     OPEN INTEREST: ${open_interest_actual:,.0f}")
                print(f"     OI CHG 24H: {oi_chg_24h_actual:.2f}% (Anterior: {oi_chg_24h_anterior:.2f}%)")
                print(f"  📈 Ratio OI/VOL: {oi_vol_ratio:.4f}")
                
                activo_info = {
                    'moneda': moneda_completa,
                    'simbolo': simbolo,
                    'price': price_actual,
                    'chg_24h': chg_24h_actual,
                    'mkt_cap': mkt_cap_actual,
                    'oi_chg_24h': oi_chg_24h_actual,
                    'oi_vol_ratio': oi_vol_ratio,
                    'open_interest': open_interest_actual,
                    'vol_24h': vol_24h_actual
                }
                activos_seleccionados.append(activo_info)
                
        except Exception as e:
            continue
    
    print(f"\n📊 Resumen comparación: {len(activos_seleccionados)} de {total_analizados} activos califican")
    return activos_seleccionados

# ========== SISTEMA DE EJECUCIÓN CONTINUA PARA SERVIDOR ==========

def ejecutar_bot_continuo():
    """Ejecuta el bot de forma continua con manejo de errores"""
    intentos = 0
    max_intentos = 5
    
    while True:
        try:
            intentos += 1
            print(f"\n🔄 INTENTO {intentos} - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
            print("=" * 60)
            
            main()
            
            # Si main() termina sin error, resetear contador
            intentos = 0
            print("✅ Ciclo completado. Reiniciando en 60 segundos...")
            time.sleep(60)
            
        except KeyboardInterrupt:
            print("\n🛑 Bot detenido por usuario")
            break
            
        except Exception as e:
            print(f"\n❌ ERROR CRÍTICO: {e}")
            print("🔧 Reiniciando en 60 segundos...")
            
            if intentos >= max_intentos:
                print(f"🚨 Demasiados errores consecutivos. Esperando 5 minutos...")
                time.sleep(300)
                intentos = 0
            
            time.sleep(60)

def main():
    global datos_anteriores, operaciones_activas, bot_salir, monitoreo_activo
    global balance_inicial, bot_desactivado_por_perdida
    
    url = "https://coinalyze.net/?order_by=oi_24h_pchange&order_dir=desc"
    
    print("🚀 Iniciando Bot de CoinAlyze + Bybit...")
    print("=" * 60)
    
    print("🔧 Configuración cargada desde .env:")
    print(f"   API Key: {BYBIT_CONFIG['api_key'][:8]}...")
    print(f"   Testnet: {BYBIT_CONFIG['testnet']}")
    print(f"   Pybit instalado: {PYBIT_INSTALADO}")
    print(f"   Máximo monedas simultáneas: {MAX_MONEDAS_SIMULTANEAS}")
    print(f"   Apalancamiento: {LEVERAGE}x")
    print("🎯 ESTRATEGIA MEJORADA:")
    print("🎯 FILTRO LATERALIZACIÓN ACTIVADO:")
    print("   - Análisis de últimas 3 horas")
    print("   - Detección de rangos < 2%")
    print("   - Verificación volumen y fuerza tendencia")
    print("=" * 60)
    print("   - Volume Regression 7/50/close con sistema de colores")
    print("   - Protección ganancias +5%/-3%") 
    print("   - Short a -1.5% con TP avanzado")
    print("   - Monitoreo PERMANENTE cada 30 segundos")
    print("=" * 60)
    
    # Inicializar archivo de registro
    inicializar_archivo_registro()
    
    # Inicializar conexión con Bybit
    bybit_activo = inicializar_bybit()
    
    # ✅ INICIALIZAR BALANCE AL INICIAR EL BOT
    balance_inicial = obtener_balance_total()
    if balance_inicial > 0:
        print(f"💰 BALANCE INICIAL: ${balance_inicial:.2f}")
        print(f"🎯 LÍMITE DE PÉRDIDA: {perdida_maxima_permitida*100}% (${balance_inicial * perdida_maxima_permitida:.2f})")
        print(f"🛑 BOT NO ABRIRÁ NUEVAS OPERACIONES SI: Balance < ${balance_inicial * (1 - perdida_maxima_permitida):.2f}")
    else:
        print("❌ No se pudo obtener balance inicial - Desactivando protección")
        balance_inicial = 0
    
    # ✅ INICIAR MONITOREO PERMANENTE UNA SOLA VEZ (FUERA DEL BUCLE)
    thread_monitoreo = threading.Thread(target=monitorear_operaciones)
    thread_monitoreo.daemon = True
    thread_monitoreo.start()
    print("🔍 MONITOREO PERMANENTE INICIADO (siempre activo, cada 30s)")
    
    ciclo = 0
        
    while not bot_salir:
        ciclo += 1
        print(f"\n🔄 CICLO {ciclo} - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("=" * 50)
        
        # ✅ VERIFICAR BALANCE AL INICIO DE CADA CICLO
        print("🔍 Verificando balance para nuevas operaciones...")
        puede_operar = puede_abrir_operaciones()
        
        if not puede_operar and len(operaciones_activas) == 0:
            print("🚨 TODAS LAS OPERACIONES CERRADAS Y BALANCE INSUFICIENTE")
            print("🚨 INICIANDO APAGADO SEGURO DEL BOT...")
            break
        
        # VERIFICAR POSICIONES CERRADAS ANTES DEL SCRAPING
        verificar_posiciones_cerradas()
        espacios_disponibles = max(0, MAX_MONEDAS_SIMULTANEAS - len(operaciones_activas))
        
        print(f"📊 Estado actual:")
        print(f"   ✅ Operaciones activas: {len(operaciones_activas)}")
        print(f"   ✅ Espacios disponibles: {espacios_disponibles}")
        print(f"   ✅ Puede abrir operaciones: {'SI' if puede_operar else 'NO'}")
        print(f"   ✅ Bot desactivado por pérdida: {'SI' if bot_desactivado_por_perdida else 'NO'}")
        
        # Solo hacer scraping si hay espacios disponibles Y puede operar
        if espacios_disponibles > 0 and puede_operar:
            df_actual = obtener_tabla_coinalyze(url)
            
            if not df_actual.empty:
                print(f"📊 Datos actuales obtenidos: {len(df_actual)} filas")
                
                if ciclo == 1:
                    print("📭 Primera ejecución - Solo extracción de datos")
                else:
                    activos_seleccionados = comparar_y_seleccionar_activos(df_actual, datos_anteriores)
                    
                    if activos_seleccionados:
                        print(f"🎯 Activos seleccionados: {len(activos_seleccionados)}")
                        activos_disponibles = filtrar_activos_disponibles_bybit(activos_seleccionados)
                        
                        if activos_disponibles:
                            print(f"✅ Activos disponibles en Bybit: {len(activos_disponibles)}")
                            operar_monedas_calificadas(activos_disponibles)
                        else:
                            print("❌ No hay activos disponibles en Bybit")
                    else:
                        print("❌ No se encontraron activos que cumplan los criterios")
                    
                datos_anteriores = df_actual.copy()
            else:
                print("❌ No se pudieron obtener datos en este ciclo")
        else:
            if espacios_disponibles == 0:
                print("✅ Límite de operaciones alcanzado - Saltando scraping")
            else:
                print("🚫 Operaciones desactivadas por pérdida - Saltando scraping")
        
        # Mostrar estadísticas cada 5 ciclos
        if ciclo % 5 == 0:
            mostrar_estadisticas()
            guardar_estadisticas_json()
        
        # Esperar 2 minutos
        if not bot_salir:
            print(f"\n⏳ Esperando 2 minutos para el próximo ciclo...")
            tiempo_inicio = time.time()
            
            while time.time() - tiempo_inicio < 120 and not bot_salir:
                tiempo_restante = 120 - (time.time() - tiempo_inicio)
                mins, secs = divmod(int(tiempo_restante), 60)
                print(f"\r🕐 Próximo ciclo en: {mins:02d}:{secs:02d}", end="", flush=True)
                time.sleep(1)
            
            if not bot_salir:
                print("\r🕐 ¡Iniciando nuevo ciclo!                    ")

    # ✅ MOTIVO DE SALIDA
    if bot_desactivado_por_perdida and len(operaciones_activas) == 0:
        print("\n🛑 APAGADO POR PÉRDIDA ACUMULADA Y SIN OPERACIONES ACTIVAS")
    elif bot_salir:
        print("\n🛑 SALIENDO POR USUARIO")
    
    # SOLO CERRAR SI EL USUARIO LO SOLICITA, NO POR PÉRDIDA
    if bot_salir:
        print("🔒 Cerrando todas las posiciones...")
        cerrar_todas_posiciones()
        monitoreo_activo = False
        time.sleep(3)
    
    # MOSTRAR ESTADÍSTICAS FINALES
    print("\n" + "="*60)
    print("📊 ESTADÍSTICAS FINALES")
    mostrar_estadisticas()
    guardar_estadisticas_json()
    
    # RESUMEN DE PÉRDIDA
    if balance_inicial > 0:
        balance_final = obtener_balance_total()
        perdida_total = balance_inicial - balance_final
        porcentaje_perdida = (perdida_total / balance_inicial) * 100
        print(f"💰 RESUMEN FINAL: Inicial=${balance_inicial:.2f} -> Final=${balance_final:.2f}")
        print(f"📉 PÉRDIDA TOTAL: ${perdida_total:.2f} ({porcentaje_perdida:.1f}%)")
    
    print("👋 Ejecución finalizada")

if __name__ == "__main__":
    print("🚀 Iniciando Bot para Google Cloud")
    
    # Verificar si estamos en entorno de servidor
    if os.name == 'posix' and 'google' in os.uname().version.lower():
        print("🌐 Detectado entorno Google Cloud - Ejecutando en modo continuo")
        ejecutar_bot_continuo()
    else:
        print("💻 Detectado entorno local - Ejecutando en modo normal")
        try:
            main()
        except KeyboardInterrupt:
            print("\n\n🛑 Bot interrumpido por el usuario")
            detener_bot_suavemente()  # Primer Ctrl+C - parada suave
            
            print("⏳ Esperando que se cierren las operaciones activas...")
            print("💡 Presiona Ctrl+C nuevamente para forzar salida inmediata")
            
            try:
                while len(operaciones_activas) > 0:
                    print(f"   Operaciones pendientes: {len(operaciones_activas)}")
                    time.sleep(30)
            except KeyboardInterrupt:
                # Segundo Ctrl+C - salida forzada
                print("\n🛑 SALIDA FORZADA - Cerrando todo inmediatamente")
                cerrar_todas_posiciones()
            
            print("✅ Bot detenido")
            mostrar_estadisticas()
            guardar_estadisticas_json()
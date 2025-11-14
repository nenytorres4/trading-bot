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

# Variables globales
datos_anteriores = None
bybit_session = None
operaciones_lock = threading.Lock()

# CONFIGURACIÓN BYBIT DESDE .ENV
BYBIT_CONFIG = {
    "api_key": os.getenv("BYBIT_API_KEY"),
    "api_secret": os.getenv("BYBIT_SECRET_KEY"),
    "testnet": os.getenv("BYBIT_TESTNET", "False").lower() == "true",
}

# Estados de operación (SIMPLIFICADO)
ESTADOS = {
    "SIN_OPERAR": 0,
    "LONG_ABIERTO": 1
}

# Tracking de operaciones activas
operaciones_activas = {}
monitoreo_activo = False

# CONFIGURACIÓN DE LÍMITES
MAX_MONEDAS_SIMULTANEAS = 1
LEVERAGE = 30
CANTIDAD_USDT = 5.5
SL_PORCENTAJE = 2  # ✅ SL al 2% como solicitaste

# Control del bot
bot_salir = False

# ========== SISTEMA DE TIMEOUT (3 HORAS DESPUÉS DE SL) ==========

# Diccionario para trackear monedas que han tocado SL
monedas_timeout = {}  # {symbol: timestamp_del_sl}

def agregar_moneda_timeout(symbol):
    """Agrega una moneda al timeout de 3 horas después de tocar SL"""
    monedas_timeout[symbol] = datetime.now()
    print(f"⏰ {symbol} agregada a timeout por 3 horas (SL activado)")

def puede_operar_moneda(symbol):
    """Verifica si una moneda puede ser operada (no está en timeout)"""
    if symbol not in monedas_timeout:
        return True
    
    tiempo_timeout = monedas_timeout[symbol]
    tiempo_actual = datetime.now()
    diferencia_horas = (tiempo_actual - tiempo_timeout).total_seconds() / 3600
    
    if diferencia_horas >= 3:
        # Timeout completado, eliminar del registro
        del monedas_timeout[symbol]
        print(f"✅ {symbol} ha completado el timeout de 3 horas - Lista para operar")
        return True
    else:
        horas_restantes = 3 - diferencia_horas
        minutos_restantes = int(horas_restantes * 60)
        print(f"⏳ {symbol} en timeout: {minutos_restantes} minutos restantes")
        return False

def limpiar_timeouts_expirados():
    """Limpia los timeouts que ya han expirado"""
    tiempo_actual = datetime.now()
    symbols_a_eliminar = []
    
    for symbol, timestamp in monedas_timeout.items():
        diferencia_horas = (tiempo_actual - timestamp).total_seconds() / 3600
        if diferencia_horas >= 3:
            symbols_a_eliminar.append(symbol)
    
    for symbol in symbols_a_eliminar:
        del monedas_timeout[symbol]
        print(f"🧹 {symbol} removida de timeout (expirado)")

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

def inicializar_archivo_registro():
    """Inicializa el archivo CSV de registro si no existe"""
    try:
        archivo = 'registro_operaciones.csv'
        if not os.path.exists(archivo):
            with open(archivo, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow([
                    'fecha_apertura', 'fecha_cierre', 'moneda', 'symbol',
                    'precio_long', 'precio_cierre', 'tipo_cierre',
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
                       tipo_cierre="", ganancia_porcentaje=0, 
                       cantidad_usdt=5.5, razon_cierre=""):
    """Registra una operación en el archivo CSV"""
    try:
        archivo = inicializar_archivo_registro()
        
        # Buscar información de la operación
        operacion = operaciones_activas.get(symbol, {})
        moneda = operacion.get('moneda', symbol.replace('USDT', ''))
        
        # Calcular duración
        fecha_apertura = operacion.get('fecha_apertura', datetime.now())
        fecha_cierre = datetime.now()
        duracion_minutos = int((fecha_cierre - fecha_apertura).total_seconds() / 60)
        
        # Obtener máximos y mínimos
        maximo_alcanzado = operacion.get('maximo_alcanzado', precio_long)
        minimo_alcanzado = operacion.get('minimo_alcanzado', precio_long)
        
        # Calcular volumen operado
        volumen_operado = cantidad_usdt
        
        # Calcular ganancia en USDT
        ganancia_usdt = cantidad_usdt * (ganancia_porcentaje / 100)
        
        with open(archivo, 'a', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerow([
                fecha_apertura.strftime('%Y-%m-%d %H:%M:%S'),
                fecha_cierre.strftime('%Y-%m-%d %H:%M:%S'),
                moneda,
                symbol,
                f"{precio_long:.8f}",
                f"{precio_cierre:.8f}",
                tipo_cierre,
                f"{ganancia_porcentaje:.4f}",
                f"{ganancia_usdt:.4f}",
                f"{cantidad_usdt:.2f}",
                duracion_minutos,
                f"{maximo_alcanzado:.8f}",
                f"{minimo_alcanzado:.8f}",
                f"{volumen_operado:.2f}",
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
                # ✅ AGREGAR AL TIMEOUT SI ES SL
                agregar_moneda_timeout(symbol)
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

        # Mostrar monedas en timeout
        if monedas_timeout:
            print(f"\n⏰ MONEDAS EN TIMEOUT (3 horas):")
            for symbol, timestamp in monedas_timeout.items():
                tiempo_actual = datetime.now()
                diferencia_horas = (tiempo_actual - timestamp).total_seconds() / 3600
                if diferencia_horas < 3:
                    horas_restantes = 3 - diferencia_horas
                    minutos_restantes = int(horas_restantes * 60)
                    print(f"   🔴 {symbol}: {minutos_restantes} minutos restantes")

def guardar_estadisticas_json():
    """Guarda las estadísticas en un archivo JSON"""
    try:
        with open('estadisticas_bot.json', 'w', encoding='utf-8') as f:
            json.dump(estadisticas, f, indent=2, ensure_ascii=False)
        print("💾 Estadísticas guardadas en estadisticas_bot.json")
    except Exception as e:
        print(f"❌ Error guardando estadísticas JSON: {e}")

# ========== SISTEMA VOLUME REGRESSION SIMPLIFICADO ==========

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
    
    # 5. Señales - SOLO VOL_DOWN (para cerrar LONG)
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
        en_rango = rango_porcentual < 2.0  # Menos del 2% de rango
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
    
    print(f"   🛡️  Protección Ganancias {symbol}:")
    print(f"      📈 Máximo alcanzado: ${maximo_alcanzado:.6f} ({((maximo_alcanzado - precio_long) / precio_long * 100):.2f}%)")
    print(f"      📉 Retroceso desde máximo: {cambio_desde_maximo:.2f}%")
    print(f"      📊 Ganancia actual: {cambio_actual:.2f}%")
    print(f"      ✅ Alcanzó +5%: {'SI' if alcanzo_5pct else 'NO'}")
    print(f"      📉 Retrocedió -3%: {'SI' if retrocedio_3pct else 'NO'}")
    print(f"      🎯 Está entre entrada y +2%: {'SI' if esta_entre_entrada_y_2pct else 'NO'}")
    
    # Si alcanzó +5% Y retrocedió -3% desde ese máximo Y está entre entrada y +2% → CERRAR
    if alcanzo_5pct and retrocedio_3pct and esta_entre_entrada_y_2pct:
        print(f"🎯 PROTECCIÓN GANANCIAS ACTIVADA: {symbol}")
        print(f"   📈 Alcanzó: +{((maximo_alcanzado - precio_long) / precio_long * 100):.2f}%")
        print(f"   📉 Retrocedió: {cambio_desde_maximo:.2f}% desde máximo")
        print(f"   💰 Ganancia actual: {cambio_actual:.2f}%")
        print(f"   ✅ Cierre entre entrada y +2%: {cambio_actual:.2f}%")
        return True
    
    return False

# ========== FUNCIONES DE CIERRE SIMPLIFICADAS ==========

def cerrar_todas_posiciones():
    """Cierra todas las posiciones abiertas"""
    global operaciones_activas
    
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
    """Cierra solo la posición LONG"""
    global operaciones_activas
    
    if not PYBIT_INSTALADO or not bybit_session:
        print(f"   📈 SIMULACIÓN: Cerrando LONG en {symbol}")
        with operaciones_lock:
            if symbol in operaciones_activas:
                del operaciones_activas[symbol]
        return True
          
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
                    del operaciones_activas[symbol]
                       
            return True
        else:
            print(f"❌ Error cerrando LONG: {response_long.get('retMsg')}")
            return False
            
    except Exception as e:
        print(f"❌ Error cerrando LONG: {e}")
        return False
    
# ========== VERIFICACIÓN DE POSICIONES CERRADAS ==========

def verificar_posiciones_cerradas():
    """Verifica si las posiciones en operaciones_activas siguen abiertas"""
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
                
                # Si no hay posiciones abiertas, eliminar del tracking
                if not posiciones_abiertas:
                    print(f"🚨 Posición cerrada detectada: {symbol}")
                    symbols_a_eliminar.append(symbol)
                    
        except Exception as e:
            print(f"❌ Error verificando posición para {symbol}: {e}")
    
    # Eliminar operaciones cerradas
    for symbol in symbols_a_eliminar:
        if symbol in operaciones_activas:
            del operaciones_activas[symbol]
            print(f"🗑️  {symbol} eliminado de operaciones activas")

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
                
                for position in positions_response['result']['list']:
                    size = float(position['size'])
                    if size > 0 and position['side'] == 'Buy':
                        long_abierto = True
                        break
                
                # Actualizar estado basado en posiciones reales
                if long_abierto:
                    operaciones_activas[symbol]['estado'] = ESTADOS["LONG_ABIERTO"]
                else:
                    # Posición cerrada - eliminar
                    print(f"🚨 Posición LONG cerrada para {symbol}")
                    del operaciones_activas[symbol]
                    
        except Exception as e:
            print(f"❌ Error actualizando estado para {symbol}: {e}")

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
                    if symbol not in operaciones_activas and side == 'Buy':
                        operaciones_activas[symbol] = {
                            'estado': ESTADOS["LONG_ABIERTO"],
                            'precio_long': float(position['avgPrice']),
                            'moneda': symbol.replace('USDT', ''),
                            'maximo_alcanzado': float(position['avgPrice']),
                            'minimo_alcanzado': float(position['avgPrice']),
                            'fecha_apertura': datetime.now()
                        }
            
            print(f"✅ Estado recuperado: {len(operaciones_activas)} operaciones")
                       
    except Exception as e:
        print(f"❌ Error recuperando estado: {e}")                

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
                            operaciones_activas[symbol]['size'] = pos_real['size']
                            operaciones_activas[symbol]['precio_long'] = pos_real['avg_price']
                            operaciones_activas[symbol]['cantidad'] = str(pos_real['size'])
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

# ========== SISTEMA DE MONITOREO SIMPLIFICADO ==========

def monitorear_operaciones():
    """Monitorea las operaciones activas CADA 30 SEGUNDOS - SIMPLIFICADO"""
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
                print(f"\n🔄 [CICLO {ciclo_monitoreo}] {datetime.now().strftime('%H:%M:%S')} - Sin operaciones activas")
                
                # ESPERA 30 SEGUNDOS CON COUNTDOWN
                print(f"⏰ Próxima verificación en:")
                tiempo_inicio = time.time()
                
                while time.time() - tiempo_inicio < 30 and not bot_salir:
                    tiempo_restante = 30 - (time.time() - tiempo_inicio)
                    mins, secs = divmod(int(tiempo_restante), 60)
                    print(f"\r   {mins:02d}:{secs:02d}", end="", flush=True)
                    time.sleep(1)
                
                if not bot_salir:
                    print("\r✅ ¡Iniciando nueva verificación!                    ")
                continue
            
            # ✅ HAY OPERACIONES ACTIVAS - MONITOREARLAS
            print(f"\n🔄 [CICLO {ciclo_monitoreo}] {datetime.now().strftime('%H:%M:%S')} - {len(operaciones_activas)} operaciones")
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
                    
                    # ✅ CALCULAR SL AL 2% COMO SOLICITASTE
                    sl_price = precio_long * (1 - SL_PORCENTAJE / 100)
                    
                    print(f"   🔍 ANALIZANDO {symbol}:")
                    print(f"      💰 Precio LONG: ${precio_long:.6f}")
                    print(f"      📊 Precio actual: ${precio_actual:.6f}")
                    print(f"      📈 Cambio: {cambio_actual:+.2f}%")
                    print(f"      🛑 Stop Loss: ${sl_price:.6f} (-{SL_PORCENTAJE}%)")
                    
                    # 1. ✅ VERIFICAR STOP LOSS (2%)
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
                                
                                if slope_price >= 0:
                                    print(f"         🟢 Fuerza Tendencial: {slope_price:.6f}")
                                else:
                                    print(f"         🔴 Fuerza Tendencial: {slope_price:.6f}")
                                
                                if slope_price < -0.0001:
                                    print(f"         🟥 🚨 SEÑAL VOL_DOWN: ACTIVA")
                                    print(f"   🟥 VOLUME REGRESSION - CERRAR LONG: {symbol}")
                                    if cerrar_posicion_long_real(symbol, "Volume Regression"):
                                        operaciones_cerradas += 1
                                    continue
                    
                    # 3. ✅ PROTECCIÓN DE GANANCIAS
                    if verificar_proteccion_ganancias(symbol, operacion, precio_actual):
                        if cerrar_posicion_long_real(symbol, "Protección Ganancias"):
                            operaciones_cerradas += 1
                        continue
                        
            # RESUMEN
            print("=" * 50)
            print(f"📊 RESUMEN: {len(operaciones_activas)} operaciones activas")
            if operaciones_cerradas > 0:
                print(f"📤 Operaciones cerradas en este ciclo: {operaciones_cerradas}")
                
            with operaciones_lock:
                for symbol, op in operaciones_activas.items():
                    estado_str = list(ESTADOS.keys())[list(ESTADOS.values()).index(op['estado'])]
                    precio_actual = obtener_precio_actual(symbol)
                    precio_long = op['precio_long']
                    cambio = ((precio_actual - precio_long) / precio_long) * 100
                    print(f"   🟡 {symbol}: {estado_str} | Cambio: {cambio:+.2f}%")
            
            # ESPERA 30 SEGUNDOS CON COUNTDOWN
            print(f"\n⏰ Próxima verificación en:")
            tiempo_inicio = time.time()
            
            while time.time() - tiempo_inicio < 30 and not bot_salir:
                tiempo_restante = 30 - (time.time() - tiempo_inicio)
                mins, secs = divmod(int(tiempo_restante), 60)
                print(f"\r   {mins:02d}:{secs:02d}", end="", flush=True)
                time.sleep(1)
            
            if not bot_salir:
                print("\r✅ ¡Iniciando nueva verificación!                    ")
            
        except Exception as e:
            print(f"❌ Error en monitoreo: {e}")
            time.sleep(30)

# ========== FUNCIONES BYBIT SIMPLIFICADAS ==========

def configurar_hedge_mode():
    """Configura el account en Hedge Mode"""
    if not PYBIT_INSTALADO or not bybit_session:
        return True
    
    try:
        print("🔧 Configurando Hedge Mode para la cuenta...")
        response = bybit_session.switch_position_mode(
            category="linear",
            mode=3  # 3 = Hedge Mode para cuentas unificadas
        )
        if response['retCode'] == 0:
            print("✅ Hedge Mode configurado correctamente")
            return True
        else:
            print(f"⚠️  Info Hedge Mode: {response.get('retMsg')}")
            return True
    except Exception as e:
        print(f"⚠️  Info Hedge Mode: {e}")
        return True

def configurar_apalancamiento(symbol):
    """Configura el apalancamiento para el símbolo"""
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
            return False
                
    except Exception as e:
        print(f"⚠️  Error configurando apalancamiento {symbol}: {e}")
        return False

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

def calcular_cantidad_segura(symbol, cantidad_usdt):
    """Calcula la cantidad de forma segura"""
    try:
        # Obtener precio
        precio = obtener_precio_actual(symbol)
        if precio == 0:
            return None, None
        
        # Obtener info del símbolo
        symbol_info = obtener_info_symbol(symbol)
        if not symbol_info:
            return None, None
        
        # VERIFICAR MÍNIMO DE ORDEN
        min_order_value = symbol_info['min_order_value']
        if cantidad_usdt < min_order_value:
            print(f"❌ Monto ${cantidad_usdt} menor que el mínimo requerido ${min_order_value}")
            return None, None
        
        # Calcular cantidad básica
        qty = cantidad_usdt / precio
        qty_step = symbol_info['qty_step']
        
        # Ajustar al step
        qty = math.floor(qty / qty_step) * qty_step
        
        # Verificar cantidad mínima
        if qty < symbol_info['min_order_qty']:
            qty = symbol_info['min_order_qty']
        
        # Formatear
        if qty >= 1 and qty == int(qty):
            qty_str = str(int(qty))
        else:
            decimal_places = len(str(qty_step).split('.')[1]) if '.' in str(qty_step) else 3
            qty_str = f"{qty:.{decimal_places}f}".rstrip('0').rstrip('.')
        
        return qty_str, precio
        
    except Exception as e:
        print(f"❌ Error calculando cantidad: {e}")
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
        qty_str, precio_actual = calcular_cantidad_segura(symbol, cantidad_usdt)
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
            return None
            
    except Exception as e:
        print(f"❌ Error en abrir_posicion_long: {e}")
        return None

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

def colocar_tp_sl(symbol, side, precio_entrada, tp_percent, sl_percent):
    """Coloca Take Profit y Stop Loss - SIMPLIFICADO"""
    if not PYBIT_INSTALADO or not bybit_session:
        print(f"   🎯 SIMULACIÓN: TP {tp_percent}%, SL {sl_percent}% para {side} en {symbol}")
        return True
    
    try:
        # Para long: SL debe ser MENOR que precio_entrada
        sl_price = precio_entrada * (1 - sl_percent / 100)
        position_idx = 1
        
        print(f"🎯 Configurando SL para {side} en {symbol}:")
        print(f"   💰 Precio entrada: {precio_entrada:.6f}")
        print(f"   🛑 SL: {sl_price:.6f} ({sl_percent}%)")
        
        # Colocar SL
        params = {
            "category": "linear",
            "symbol": symbol,
            "stopLoss": str(round(sl_price, 6)),
            "slTriggerBy": "MarkPrice",
            "positionIdx": position_idx
        }
        
        response = bybit_session.set_trading_stop(**params)
        
        if response['retCode'] == 0:
            print(f"✅ SL colocado para {side} en {symbol}")
            return True
        else:
            print(f"❌ Error colocando SL: {response.get('retMsg', 'Unknown error')}")
            return False
            
    except Exception as e:
        print(f"❌ Error colocando SL: {e}")
        return False

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

# ========== ESTRATEGIA SIMPLIFICADA ==========

def obtener_datos_para_volume_regression(symbol, periodo='5', limite=100):
    """Obtiene datos de OHLCV para calcular Volume Regression"""
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
            limit=limite
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
    """Inicializa la conexión con Bybit"""
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
            
            # Configurar Hedge Mode
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
    """Filtra los activos seleccionados que están disponibles en Bybit"""
    print("\n🔍 VERIFICANDO DISPONIBILIDAD EN BYBIT...")
    
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
        
        if simbolo_bybit in pares_bybit:
            tiene_operaciones, motivo = verificar_operaciones_abiertas(simbolo_bybit)
            if not tiene_operaciones:
                activo['simbolo_bybit'] = simbolo_bybit
                activos_disponibles.append(activo)
                print(f"   ✅ {moneda} ({simbolo}) -> {simbolo_bybit}: Disponible")
            else:
                print(f"   ⚠️  {moneda} ({simbolo}) -> {simbolo_bybit}: {motivo}")
        else:
            print(f"   ❌ {moneda} ({simbolo}) -> {simbolo_bybit}: No disponible")
    
    print(f"\n📊 Resumen Bybit: {len(activos_disponibles)} de {len(activos_seleccionados)} activos disponibles")
    return activos_disponibles

def operar_monedas_calificadas(activos_disponibles):
    """Ejecuta las operaciones para las monedas que califican - CON FILTRO LATERAL Y TIMEOUT"""
    global operaciones_activas
    
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
        
        # ✅ VERIFICAR SI LA MONEDA ESTÁ EN TIMEOUT (3 HORAS DESPUÉS DE SL)
        if not puede_operar_moneda(symbol):
            print(f"   ⏰ {moneda} ({symbol}): En timeout por SL reciente - Saltando")
            continue
        
        print(f"\n📈 Operando {moneda} ({symbol})...")
        
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
        
        # Abrir posición LONG (5.5 USDT)
        print(f"   🚀 Abriendo posición LONG...")
        order_id_long = abrir_posicion_long(symbol, 5.5)
        
        if order_id_long:
            # Obtener precio actual para el registro
            precio_actual = obtener_precio_actual(symbol)
            
            # Registrar operación con fecha de apertura
            operaciones_activas[symbol] = {
                'estado': ESTADOS["LONG_ABIERTO"],
                'precio_long': precio_actual,
                'order_id_long': order_id_long,
                'moneda': moneda,
                'maximo_alcanzado': precio_actual,
                'minimo_alcanzado': precio_actual,
                'fecha_apertura': datetime.now()
            }
            
            # Colocar SL al 2% como solicitaste - SIN TP
            colocar_tp_sl(symbol, "Buy", precio_actual, 0, SL_PORCENTAJE)
            
            print(f"   ✅ LONG establecido para {symbol} a ${precio_actual:.6f}")
            monedas_operadas += 1
    
    print(f"\n📈 RESUMEN OPERACIONES: {monedas_operadas} monedas operadas")
    print(f"📊 Total operaciones activas: {len(operaciones_activas)}")

# ========== FUNCIONES DE SCRAPING (sin cambios) ==========

def obtener_tabla_coinalyze(url):
    """Obtiene la tabla de datos de CoinAlyze usando Selenium"""
    options = Options()
    options.add_argument('--headless')
    options.add_argument('--no-sandbox')
    options.add_argument('--disable-dev-shm-usage')
    options.add_argument('--disable-blink-features=AutomationControlled')
    options.add_argument('--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36')
    
    try:
        from webdriver_manager.chrome import ChromeDriverManager
        service = Service(ChromeDriverManager().install())
    except ImportError:
        import subprocess
        subprocess.check_call(['pip', 'install', 'webdriver-manager'])
        from webdriver_manager.chrome import ChromeDriverManager
        service = Service(ChromeDriverManager().install())
    
    driver = webdriver.Chrome(service=service, options=options)
    
    try:
        print("Cargando página...")
        driver.get(url)
        wait = WebDriverWait(driver, 20)
        time.sleep(8)
        
        print("Buscando tabla de datos...")
        table_selectors = [
            "//table",
            "//div[contains(@class, 'table')]//table",
            "//table[contains(@class, 'table')]",
            "//*[@id='root']//table",
            "//div[@id='root']//table"
        ]
        
        table_elem = None
        for selector in table_selectors:
            try:
                table_elem = wait.until(EC.presence_of_element_located((By.XPATH, selector)))
                print(f"Tabla encontrada con selector: {selector}")
                break
            except:
                continue
        
        if not table_elem:
            raise Exception("No se pudo encontrar la tabla en la página")
        
        # Obtener headers
        headers = []
        try:
            header_row = table_elem.find_element(By.TAG_NAME, "thead")
            header_cells = header_row.find_elements(By.TAG_NAME, "th")
            headers = [cell.text.strip() for cell in header_cells if cell.text.strip()]
            print(f"✅ Headers encontrados: {headers}")
        except Exception as e:
            print(f"❌ Error obteniendo headers: {e}")
            return pd.DataFrame()
        
        # Obtener datos
        datos = []
        try:
            tbody = table_elem.find_element(By.TAG_NAME, "tbody")
            rows = tbody.find_elements(By.TAG_NAME, "tr")
            print(f"📊 Se encontraron {len(rows)} filas de datos")
            
            for i, row in enumerate(rows):
                try:
                    cells = row.find_elements(By.TAG_NAME, "td")
                    if cells:
                        fila_datos = [cell.text.strip() for cell in cells]
                        if fila_datos and fila_datos[0] == '':
                            fila_datos = fila_datos[1:]
                        if len(fila_datos) > len(headers):
                            fila_datos = fila_datos[:len(headers)]
                        elif len(fila_datos) < len(headers):
                            fila_datos.extend([''] * (len(headers) - len(fila_datos)))
                        datos.append(fila_datos)
                except:
                    continue
                    
        except Exception as e:
            print(f"❌ Error obteniendo datos del tbody: {e}")
            return pd.DataFrame()
        
        # Crear DataFrame
        if datos:
            df = pd.DataFrame(datos, columns=headers)
            print(f"✅ DataFrame creado con {len(df)} filas y {len(df.columns)} columnas")
            
            # MOSTRAR LISTA DE MONEDAS ENCONTRADAS EN COINALYZE ({len(df)}):")
            print("=" * 70)
            for i, (idx, fila) in enumerate(df.iterrows(), 1):
                moneda = str(fila['COIN'])
                price = str(fila['PRICE'])
                chg_24h = str(fila['CHG 24H'])
                mkt_cap = str(fila['MKT CAP'])
                simbolo = extraer_simbolo_de_moneda(moneda)
                simbolo_str = f"({simbolo})" if simbolo else "(sin símbolo)"
                print(f"{i:3d}. {moneda:25} {simbolo_str:15} | Price: {price:10} | CHG: {chg_24h:8} | MKT CAP: {mkt_cap:10}")
            
            return df
        else:
            print("❌ No se encontraron datos en la tabla")
            return pd.DataFrame()
            
    except Exception as e:
        print(f"❌ Error durante el scraping: {e}")
        driver.save_screenshot("coinalyze_error.png")
        print("Screenshot guardado como 'coinalyze_error.png'")
        return pd.DataFrame()
    
    finally:
        driver.quit()

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

def main():
    global datos_anteriores, operaciones_activas, bot_salir, monitoreo_activo
    
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
    print("🎯 TIMEOUT POR SL ACTIVADO:")
    print(f"   - Monedas con SL reciente: 3 horas sin operar")
    print("=" * 60)
    print("   - Volume Regression 7/50/close con sistema de colores")
    print("   - Protección ganancias +5%/-3%") 
    print(f"   - Stop Loss al {SL_PORCENTAJE}%")
    print("   - Monitoreo PERMANENTE cada 30 segundos")
    print("=" * 60)
    
    # Inicializar archivo de registro
    inicializar_archivo_registro()
    
    # Inicializar conexión con Bybit
    bybit_activo = inicializar_bybit()
    
    # ✅ INICIAR MONITOREO PERMANENTE UNA SOLA VEZ
    thread_monitoreo = threading.Thread(target=monitorear_operaciones)
    thread_monitoreo.daemon = True
    thread_monitoreo.start()
    print("🔍 MONITOREO PERMANENTE INICIADO (siempre activo, cada 30s)")
    
    ciclo = 0
        
    while not bot_salir:
        ciclo += 1
        print(f"\n🔄 CICLO {ciclo} - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("=" * 50)
        
        # LIMPIAR TIMEOUTS EXPIRADOS
        limpiar_timeouts_expirados()
        
        # VERIFICAR POSICIONES CERRADAS ANTES DEL SCRAPING
        verificar_posiciones_cerradas()
        espacios_disponibles = MAX_MONEDAS_SIMULTANEAS - len(operaciones_activas)
        print(f"📊 Espacios disponibles: {espacios_disponibles}")
        print(f"📈 Operaciones activas: {len(operaciones_activas)}")

        # Mostrar estado actual de operaciones
        if operaciones_activas:
            print("\n📋 OPERACIONES ACTIVAS:")
            with operaciones_lock:
                for symbol, op in operaciones_activas.items():
                    estado_str = list(ESTADOS.keys())[list(ESTADOS.values()).index(op['estado'])]
                    precio_actual = obtener_precio_actual(symbol)
                    precio_entrada = op.get('precio_long', 0)
                    if precio_entrada > 0:
                        cambio = ((precio_actual - precio_entrada) / precio_entrada) * 100
                        print(f"   - {symbol}: {estado_str} | Cambio: {cambio:+.2f}%")
                    else:
                        print(f"   - {symbol}: {estado_str}")
        
        # Solo hacer scraping si hay espacios disponibles
        if espacios_disponibles > 0:
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
            print("✅ Límite de operaciones alcanzado - Saltando scraping")
        
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

    # LIMPIAR AL SALIR
    if bot_salir:
        print("\n🛑 SALIENDO - Cerrando todas las posiciones...")
        cerrar_todas_posiciones()
        monitoreo_activo = False
        time.sleep(3)  # Dar tiempo para que se cierren las posiciones
    
    # MOSTRAR ESTADÍSTICAS FINALES
    print("\n" + "="*60)
    print("📊 ESTADÍSTICAS FINALES")
    mostrar_estadisticas()
    guardar_estadisticas_json()
    print("👋 Ejecución finalizada")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n🛑 Bot interrumpido por el usuario")
        bot_salir = True
        mostrar_estadisticas()
        guardar_estadisticas_json()
    except Exception as e:
        print(f"\n\n❌ Error crítico: {e}")
        bot_salir = True
        mostrar_estadisticas()
        guardar_estadisticas_json()
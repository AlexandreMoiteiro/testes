# NAVLOG Portugal — VFR + IFR Low

Streamlit app para navlogs VFR/IFR low em Portugal continental.

## Ficheiros esperados no repo

- `app.py`
- `AD-HEL-ULM.csv`
- `Localidades-Nova-versao-230223.csv`
- `NAVAIDS_VOR.csv`
- `NAVLOG_FORM.pdf`
- `NAVLOG_FORM_1.pdf`
- `IFR_POINTS.csv` — pontos IFR ENR 4.4
- `IFR_AIRWAYS.csv` — sequências de airways ENR 3.3

A app nunca vai ao AIP em runtime. Para atualizar dados IFR manualmente:

```bash
pip install -r requirements.txt
python tools/update_ifr_data.py
```

Depois valida os CSV e faz commit.

## Sintaxe de rota

- Direto: `LPSO MAGUM ATECA LPFR`
- Airway: `MAGUM UZ218 ATECA`
- VOR radial/distance: `CAS/R180/D12` ou `CAS-R180-D12`
- Coordenada decimal: `38.70,-9.15`
- ICAO lat/lon compacto: `3839N00837W`

## Aviso

Ferramenta de planeamento. Confirmar sempre AIP/AIRAC, NOTAM, cartas, mínimos, meteorologia e autorizações ATC antes de voo.

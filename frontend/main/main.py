from fastapi import FastAPI, WebSocket
import asyncio

app = FastAPI()

i = 0
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    global i
    await websocket.accept()
    while True:
        await websocket.send_text(f"[{i}] Hi From Server")
        i += 1
        await asyncio.sleep(1)  # Wait for 1 second

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)

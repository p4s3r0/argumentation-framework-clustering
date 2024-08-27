<template>
  <div>
    <h1>WebSocket Stream</h1>
    <div v-for="(message, index) in messages" :key="index">{{ message }}</div>
  </div>
</template>

<script>
export default {
  data() {
    return {
      ws: null,
      messages: []
    };
  },
  mounted() {
    // Connect to WebSocket server
    this.ws = new WebSocket('ws://localhost:8000/ws');

    // Listen for messages
    this.ws.onmessage = (event) => {
      this.messages.push(event.data);
    };

    // Log connection status
    this.ws.onopen = () => {
      console.log('WebSocket connection established.');
    };

    this.ws.onclose = () => {
      console.log('WebSocket connection closed.');
    };
  },
  beforeDestroy() {
    // Close WebSocket connection when the component is destroyed
    if (this.ws) {
      this.ws.close();
    }
  }
};
</script>
